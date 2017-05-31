/*author: Zhao Zihan & Liu Siyuan*/
#include <stdio.h>
#include <stdlib.h> 
#include <assert.h>

#include "absyn.h"
#include "types.h"
#include "temp.h"
#include "tree.h"
#include "frame.h"
#include "translate.h"
#include "env.h"


#include "errormsg.h"
#include "semant.h"

struct expty 
{
	/*Tree Structure in translate.c*/
	Tr_exp exp; 
	/*Type Structure*/
	Ty_ty ty; 
};

/*expty constructor*/
struct expty expTy(Tr_exp exp, Ty_ty ty)
{
	struct expty et;

	et.exp = exp;
	et.ty = ty;

	return et;
}

/*-----------------------------------------------------------------------------------------------------*/
/*recursive function of absyn tree*/
static struct expty transVar(Tr_level level, Tr_exp breakk,S_table venv, S_table tenv, A_var v);
static struct expty transExp(Tr_level level, Tr_exp breakk, Tr_exp venv, S_table tenv, A_exp e);
static		 Tr_exp transDec(Tr_level level, Tr_exp breakk, Tr_exp venv, S_table tenv, A_dec d);
static		  Ty_ty	transTy(											 S_table tenv, A_ty  t);

/*-----------------------------------------------------------------------------------------------------*/
/*Functions Within the module*/
/*return real type in Ty_ty in case of Ty_name*/
static Ty_ty actual_ty(Ty_ty);
static Ty_tyList makeFormalTyList(S_table, A_fieldList); /*may use #define*/
static bool args_match(Tr_level, Tr_exp, S_table, S_table, A_expList, Ty_tyList, A_exp); /*may use #define*/
static bool ty_match(Ty_ty, Ty_ty);
static bool efields_match(Tr_level, Tr_exp, S_table, S_table, Ty_ty, A_exp); /*may use #define*/
static Ty_fieldList makeFieldTys(S_table, A_fieldList); /*may use #define*/
static U_boolList makeFormals(A_fieldList); /*may use #define*/

/*-----------------------------------------------------------------------------------------------------*/

F_fragList SEM_transProg(A_exp exp) {
	struct expty et;
	S_table t = E_base_tenv();
	S_table v = E_base_venv();
	et = transExp(Tr_outermost(), NULL, v, t, exp);
	F_fragList resl = Tr_getResult();
	return resl;
}

static struct expty transVar(Tr_level level, Tr_exp breakk,S_table venv, S_table tenv, A_var v) 
{
	/*empty*/
	if (!v)
		return expTy(Tr_noExp(), Ty_Void());

	E_enventry x;
	Tr_exp var;
	struct expty ExpTy;

	switch (v->kind) 
	{
	/* var id. i.e.: a */
	case A_simpleVar:
	{
		x = S_look(venv, v->u.simple);
		var = Tr_noExp();
		if (x && x->kind == E_varEntry) 
		{
			var = Tr_simpleVar(x->u.var.access, level);
			return expTy(var, actual_ty(x->u.var.ty));
		}
		else 
		{
			EM_error(v->pos, "Undefined variable %s.", S_name(v->u.simple));
			return expTy(var, Ty_Int());
		}
	}
	/* var record. i.e.: a.b */
	case A_fieldVar:
	{
		ExpTy = transVar(level, breakk, venv, tenv, v->u.field.var);
		var = Tr_noExp();
		if (ExpTy.ty->kind != Ty_record)
		{
			EM_error(v->pos, "Not a record type!");
		}
		/*Ty_fieldList*/
		else 
		{
			Ty_fieldList fieldList;
			int field_offset = 0;
			for (fieldList = ExpTy.ty->u.record; fieldList; fieldList = fieldList->tail, field_offset++)
			{ 
				/*match with symbol table*/
				if (fieldList->head->name == v->u.field.sym)
				{
					var = Tr_fieldVar(ExpTy.exp, field_offset);
					return expTy(var, actual_ty(fieldList->head->ty));
				}
			}
			EM_error(v->pos, "field /'%s/' doesn't exist.", S_name(v->u.field.sym));
		}
		/*why not void?*/
		return expTy(var, Ty_Int());
	}
	/* var array. i.e.: a[b] */
	case A_subscriptVar: 
	{
		ExpTy = transVar(level, breakk, venv, tenv, v->u.subscript.var);
		var = Tr_noExp();
		struct expty ExpTy_2;
		if (ExpTy.ty->kind != Ty_array) 
		{
			EM_error(v->pos, "Not an array type!");
		}
		else 
		{
			ExpTy_2 = transExp(level, breakk, venv, tenv, v->u.subscript.exp);
			/*subscript requires int type*/
			if (ExpTy_2.ty->kind != Ty_int) 
			{
				EM_error(v->pos, "Subscript requires int type!");
			}
			else 
			{
				var = Tr_subscriptVar(ExpTy.exp, ExpTy_2.exp);
				return expTy(var, actual_ty(ExpTy.ty->u.array));
			}
		}
		return expTy(var, Ty_Int());
	}
	default:
		assert(0);
	}
}

static struct expty transExp(Tr_level level, Tr_exp breakk, Tr_exp venv, S_table tenv, A_exp e) 
{
	/*Empty*/
	if (!e)
		return expTy(Tr_noExp(), Ty_Void());

	switch (e->kind)
	{
	case A_varExp:
	{
		return transVar(level, breakk, venv, tenv, e->u.var);
	}
	case A_nilExp:
	{
		return expTy(Tr_nilExp(), Ty_Nil());
	}
	case A_intExp:
	{
		return expTy(Tr_intExp(e->u.intt), Ty_Int());
	}
	case A_stringExp:
	{
		return expTy(Tr_stringExp(e->u.stringg), Ty_String());
	}
	/*questions*/
	case A_callExp:
	{
		E_enventry callEnv = S_look(venv, e->u.call.func);
		A_expList args = NULL;
		Tr_expList argList = NULL;
		for (args = e->u.call.args; args; args = args->tail)
		{
			struct expty arg = transExp(level, breakk, venv, tenv, args->head);
			/*action: */
			Tr_expList_annotate(arg.exp, &argList);
		}
		Tr_exp trans = Tr_noExp();
		if (callEnv && callEnv->kind == E_funEntry)
		{
			trans = Tr_callExp(callEnv->u.fun.label, callEnv->u.fun.level, level, &argList);
			if (args_match(level, breakk, venv, tenv, e->u.call.args, callEnv->u.fun.formals, e))
			{
				if (callEnv->u.fun.result)
				{
					return expTy(trans, actual_ty(callEnv->u.fun.result));
				}
			}
		}
		else
		{
			EM_error(e->pos, "Function %s is undefined!\n", S_name(e->u.call.func));
		}
		return expTy(trans, Ty_Void());
	}
	case A_opExp:
	{
		A_oper oper = e->u.op.oper;
		struct expty left = transExp(level, venv, tenv, breakk, e->u.op.left);
		struct expty right = transExp(level, venv, tenv, breakk, e->u.op.right);
		Tr_exp Trans = Tr_noExp();
		switch (oper)
		{
		case A_plusOp:
		case A_minusOp:
		case A_timesOp:
		case A_divideOp:
			if (left.ty->kind != Ty_int)
				EM_error(e->u.op.left->pos, "left-hand side type %s: expected int",
					Ty_String(left.ty));//?
			if (right.ty->kind != Ty_int)
				EM_error(e->u.op.right->pos, "right-hand side type %s: expected int",
					Ty_String(right.ty));
			return expTy(Tr_binOpExp(oper, left.exp, right.exp), Ty_Int());
			/*questions*/
			/* == and != */
		case A_eqOp:
		case A_neqOp:
			switch (left.ty->kind)
			{
			case Ty_int:
				if (is_equal_ty(right.ty, left.ty))
					/*action:*/
					Trans = Tr_relOpExp(oper, left.exp, right.exp);
				break;
			case Ty_string:
				if (is_equal_ty(right.ty, left.ty))
					/*action:*/
					Trans = Tr_eqStringExp(oper, left.exp, right.exp);
				break;
			case Ty_array:
			{
				if (right.ty->kind != left.ty->kind)
				{
					EM_error(e->u.op.right->pos,
						"left - hand side type %s: expected %s",
						Ty_String(right.ty), Ty_String(left.ty));
				}
				/*action:*/
				Trans = Tr_relOpExp(oper, left.exp, right.exp);
				break;
			}
			case Ty_record:
			{
				if (right.ty->kind != Ty_record && right.ty->kind != Ty_nil)
				{
					EM_error(e->u.op.right->pos,
						"right - hand side type %s: expected record or nil",
						Ty_String(right.ty));
				}
				/*action:*/
				Trans = Tr_relOpExp(oper, left.exp, right.exp);
				break;
			}
			default:
			{
				EM_error(e->u.op.right->pos, "Unexpected %s expression in equation or inquation.",
					Ty_String(right.ty));
			}
			}
			return expTy(Trans, Ty_Int());
		case A_ltOp:
		case A_leOp:
		case A_gtOp:
		case A_geOp:
		{
			if (right.ty->kind != left.ty->kind)
			{
				EM_error(e->u.op.right->pos,
					"%s expression given for RHS; expected %s",
					Ty_String(right.ty), Ty_String(left.ty));
			}
			switch (left.ty->kind) 
			{
			case Ty_int:
				Trans = Tr_relOpExp(oper, left.exp, right.exp); break;
			case Ty_string:
				Trans = Tr_noExp(); break;
			default:
			{
				EM_error(e->u.op.right->pos, "unexpected type %s in comparsion",
					Ty_String(right.ty));
				Trans = Tr_noExp();
			}
			}
			return expTy(Trans, Ty_Int());
		}
		}
		assert(0 && "Invalid operator in expression");
		return expTy(Tr_noExp(), Ty_Int());
	}
	/*questions*/
	case A_recordExp:
	{
		Ty_ty recty = actual_ty(S_look(tenv, e->u.record.typ));
		/*cant find record-type in table tenv*/
		if (!recty)
		{
			EM_error(e->pos, "undefined type %s (debug recordExp)", S_name(e->u.record.typ));
		}
		else
		{
			if (recty->kind != Ty_record)
			{
				EM_error(e->pos, "%s is not a record type", S_name(e->u.record.typ));
				return expTy(Tr_noExp(), Ty_Record(NULL));
			}
			/*check record field is matched*/
			if (efields_match(level, breakk, venv, tenv, recty, e))
			{
				Tr_expList l = NULL;
				int n = 0;
				A_efieldList el;
				for (el = e->u.record.fields; el; el = el->tail, n++)
				{
					struct expty val = transExp(level, breakk, venv, tenv, el->head->exp);
					Tr_expList_annotate(val.exp, &l);
				}
				return expTy(Tr_recordExp(n, l), recty);
			}
		}
		return expTy(Tr_noExp(), Ty_Record(NULL));
	}
	case A_seqExp:
	{
		Tr_expList l = NULL;
		A_expList list = e->u.seq;
		struct expty seqone;
		if (!list) {
			return expTy(Tr_noExp(), Ty_Void());
		}
		for (; list; list = list->tail) {
			seqone = transExp(level, breakk, venv, tenv, list->head);
			Tr_expList_annotate(seqone.exp, &l);
		}
		return expTy(Tr_seqExp(l), seqone.ty);
	}
	case A_assignExp:
	{
		struct expty final4 = transVar(level, breakk, venv, tenv, e->u.assign.var);
		struct expty final5 = transExp(level, breakk, venv, tenv, e->u.assign.exp);
		if (!ty_match(final4.ty, final5.ty)) {
			EM_error(e->pos, "unmatched assign exp");
		}
		return expTy(Tr_assignExp(final4.exp, final5.exp), Ty_Void());
	}
	case A_ifExp:
	{
		struct expty final = transExp(level, breakk, venv, tenv, e->u.iff.test);
		struct expty final2 = transExp(level, breakk, venv, tenv, e->u.iff.then);
		struct expty final3 = { NULL, NULL };
		if (e->u.iff.elsee) { /*no else-part*/
			final3 = transExp(level, breakk, venv, tenv, e->u.iff.elsee);
			if (final.ty->kind != Ty_int) {
				EM_error(e->u.iff.test->pos, "int required");
			}
			if (!ty_match(final2.ty, final3.ty)) {
				EM_error(e->pos, "if-else sentence must return same type");
			}
		}
		return expTy(Tr_ifExp(final.exp, final2.exp, final3.exp), final2.ty);
	}
	case A_whileExp:
	{
		struct expty final = transExp(level, breakk, venv, tenv, e->u.whilee.test);
		if (final.ty->kind != Ty_int) {
			EM_error(e->pos, "int required");
		}
		Tr_exp done = Tr_doneExp();
		struct expty body = transExp(level, done, venv, tenv, e->u.whilee.body);
		return expTy(Tr_whileExp(final.exp, body.exp, done), Ty_Void());
	}
	case A_forExp:
	{
		EM_error(e->pos, "\nsome one said for is better than while\nmake them unhappy \nahahaha");
		return expTy(Tr_noExp(), Ty_Int());
	}
	case A_breakExp:
	{
		if (!breakk)
			return expTy(Tr_noExp(), Ty_Void());
		return expTy(Tr_breakExp(breakk), Ty_Void());
	}
	case A_letExp:
	{
		A_decList decs;
		Tr_expList l = NULL;
		S_beginScope(venv);
		S_beginScope(tenv);
		for (decs = e->u.let.decs; decs; decs = decs->tail) {
			Tr_expList_annotate(transDec(level, breakk, venv, tenv, decs->head), &l);
		}
		struct expty final = transExp(level, breakk, venv, tenv, e->u.let.body);
		Tr_expList_annotate(final.exp, &l);
		S_endScope(venv);
		S_endScope(tenv);
		return expTy(Tr_seqExp(l), final.ty);
	}
	case A_arrayExp:
	{
		Ty_ty arrayty = actual_ty(S_look(tenv, e->u.array.typ));
		if (!arrayty)
		{
			EM_error(e->pos, "undeined array type %s", S_name(e->u.array.typ));
			return expTy(Tr_noExp(), Ty_Int());
		}
		if (arrayty->kind != Ty_array)
		{
			EM_error(e->pos, "%s is not a array type", S_name(e->u.array.typ));
			return expTy(Tr_noExp(), Ty_Int());
		}
		struct expty final2 = transExp(level, breakk, venv, tenv, e->u.array.size);
		struct expty final3 = transExp(level, breakk, venv, tenv, e->u.array.init);
		if (final2.ty->kind != Ty_int)
		{
			EM_error(e->pos, "array size should be int %s", S_name(e->u.array.typ));
		}
		else if (!ty_match(final3.ty, arrayty->u.array))
		{
			EM_error(e->pos, "unmatched array type in %s", S_name(e->u.array.typ));
		}
		else
		{
			return expTy(Tr_arrayExp(final2.exp, final3.exp), arrayty);
		}
		return expTy(Tr_noExp(), Ty_Int());
	}
	default:
	{
		assert(0);
	}
	}
}

static		 Tr_exp transDec(Tr_level level, Tr_exp breakk, Tr_exp venv, S_table tenv, A_dec d) {

	struct expty res_exp;
	Tr_access tr_access;
	Ty_ty res_ty;

	switch (d->kind)
	{
	case A_varDec:
	{
		res_exp = transExp(level, breakk, venv, tenv, d->u.var.init);
		tr_access = Tr_allocLocal(level, d->u.var.escape);	//allocate local variable, return the position
		if (!d->u.var.typ)
		{
			if (res_exp.ty->kind == Ty_nil || res_exp.ty->kind == Ty_void)
			{
				EM_error(d->pos, "init should not be nil without type in %s", S_name(d->u.var.var));
				S_enter(venv, d->u.var.var, E_VarEntry(tr_access, Ty_Int()));
			}
			else
			{
				S_enter(venv, d->u.var.var, E_VarEntry(tr_access, res_exp.ty));
			}
		}
		else
		{
			res_ty = S_look(tenv, d->u.var.typ);
			if (!res_ty)
			{
				EM_error(d->pos, "undifined type %s", S_name(d->u.var.typ));
			}
			else
			{
				if (!ty_match(res_ty, res_exp.ty))
				{
					EM_error(d->pos, "unmatched type in %s", S_name(d->u.var.typ));
					S_enter(venv, d->u.var.var, E_VarEntry(tr_access, res_ty));
				}
				else
				{
					S_enter(venv, d->u.var.var, E_VarEntry(tr_access, res_ty));
				}
			}
		}
		Tr_exp tr_var = Tr_simpleVar(tr_access, level);
		return Tr_assignExp(tr_var, res_exp.exp);
	}
	case A_functionDec:
	{
		A_fundecList func_list = d->u.function;
		Ty_tyList formalTys;
		struct expty res_body;
		while (func_list)
		{
			if (func_list->head->result)
			{
				res_ty = S_look(tenv, func_list->head->result);
				if (!res_ty)
				{
					EM_error(func_list->head->pos, "undefined type for return type");
					res_ty = Ty_Void();
				}
			}
			else
			{
				res_ty = Ty_Void();
			}
			formalTys = makeFormalTyList(tenv, func_list->head->params);
			Temp_label fun_label = Temp_newlabel();
			Tr_level tr_level = Tr_newLevel(level, fun_label, makeFormals(func_list->head->params));/* create a new level */
			S_enter(venv, func_list->head->name, E_FunEntry(tr_level, fun_label, formalTys, res_ty));
			func_list = func_list->tail;
		}

		func_list = d->u.function;
		A_fundec f;
		A_fieldList param;
		Ty_tyList ty_list;
		Tr_accessList tr_acclist;
		while (func_list)
		{
			f = func_list->head;
			E_enventry fun_info = S_look(venv, f->name);

			S_beginScope(venv);
			formalTys = fun_info->u.fun.formals;

			tr_acclist = Tr_formals(fun_info->u.fun.level);
			param = f->params;
			ty_list = formalTys;
			while (param && ty_list && tr_acclist)
			{
				S_enter(venv, param->head->name, E_VarEntry(tr_acclist->head, ty_list->head));
				param = param->tail;
				ty_list = ty_list->tail;
				tr_acclist = tr_acclist->tail;
			}

			res_body = transExp(fun_info->u.fun.level, breakk, venv, tenv, f->body);
			E_enventry fun = S_look(venv, f->name);
			if (!ty_match(fun->u.fun.result, res_body.ty))
			{
				EM_error(f->pos, "incorrect return type in function '%s'", S_name(f->name));
			}
			Tr_procEntryExit(fun_info->u.fun.level, res_body.exp, tr_acclist);
			S_endScope(venv);

			func_list = func_list->tail;
		}
		return Tr_noExp();
	}
		
	case A_typeDec:
	{
		A_nametyList name_list = d->u.type;
		Ty_ty res_ty, name_ty;
		int cycle;
		while (name_list)
		{
			S_enter(tenv, name_list->head->name, Ty_Name(name_list->head->name, NULL));
			name_list = name_list->tail;
		}

		cycle = TRUE;
		name_list = d->u.type;
		while (name_list)
		{
			res_ty = transTy(tenv, name_list->head->ty);
			if (cycle)
			{
				if (res_ty->kind != Ty_name)
				{
					cycle = FALSE;
				}
			}
			if (!name_list->tail && res_ty->kind != Ty_name)
			{
				/*line num is some bug*/
				EM_error(d->pos, "warning: actual type should declare before nameTy type");
			}
			name_ty = S_look(tenv, name_list->head->name);
			name_ty->u.name.ty = res_ty;

			name_list = name_list->tail;
		}
		if (cycle)
			EM_error(d->pos, "illegal type cycle: cycle must contain record, array");
		return Tr_noExp();
	}
	default:
		assert(0);
	}
}

static        Ty_ty transTy (                                            S_table tenv, A_ty t)
{
	Ty_ty res = NULL;
	Ty_fieldList f_list;

	switch (t->kind)
	{
	case A_nameTy:
	{
		res = S_look(tenv, t->u.name);
		if (!res)
		{
			EM_error(t->pos, "undefined type %s", S_name(t->u.name));
			return Ty_Int();
		}
		return res;
	}
	case A_recordTy:
	{
		f_list = makeFieldTys(tenv, t->u.record);
		return Ty_Record(f_list);
	}
	case A_arrayTy:
	{
		res = S_look(tenv, t->u.array);
		if (!res)
			EM_error(t->pos, "undefined type %s", S_name(t->u.array));
		return Ty_Array(res);
	}
	default:
		assert(0);
	}
}

/*-----------------------------------------------------------------------------------------------------*/
/*Functions within the module*/
static Ty_ty actual_ty(Ty_ty ty)
{
	if (ty->kind == Ty_name)
		actual_ty(ty->u.name.ty);
	else return ty;
}

static Ty_tyList makeFormalTyList(S_table t, A_fieldList f_list)
{
	Ty_tyList head = NULL, list = NULL;
	A_fieldList fl = f_list;
	Ty_ty ty;
	while (fl)
	{
		ty = S_look(t, fl->head->typ);

		if (!ty)
		{
			EM_error(fl->head->pos, "undefined type %s", S_name(fl->head->typ));
			ty = Ty_Int();
		}
		if (!head)
		{
			head = Ty_TyList(ty, NULL);
			list = head;
		}
		else
		{
			list->tail = Ty_TyList(ty, NULL);
			list = list->tail;
		}
		fl = fl->tail;
	}

	return head;
}

static Ty_fieldList makeFieldTys(S_table t, A_fieldList fieldlist)
{
	A_fieldList f_list = fieldlist;
	Ty_fieldList head = NULL, list;
	Ty_ty ty;
	Ty_field field;
	while (f_list)
	{
		ty = S_look(t, f_list->head->typ);
		if (!ty)
		{
			EM_error(f_list->head->pos, "undefined type %s", S_name(f_list->head->typ));
		}
		else
		{
			field = Ty_Field(f_list->head->name, ty);
			if (head)
			{
				list->tail = Ty_FieldList(field, NULL);
				list = list->tail;
			}
			else
			{
				head = Ty_FieldList(field, NULL);
				list = head;
			}
		}
		f_list = f_list->tail;
	}
	return head;
}

static U_boolList makeFormals(A_fieldList params)
{
	U_boolList head, list;
	A_fieldList fl = params;
	head = list = NULL;
	while (fl)
	{
		if (head)
		{
			list->tail = U_BoolList(TRUE, NULL);
			list = list->tail;
		}
		else
		{
			head = U_BoolList(TRUE, NULL);
			list = head;
		}
		fl = fl->tail;
	}
	return head;
}

static bool args_match(Tr_level level, Tr_exp breakk, S_table v, S_table tt, A_expList ell, Ty_tyList fll, A_exp fun) {
	struct expty t;
	A_expList el = ell;
	Ty_tyList fl = fll;

	while (el && fl) {
		t = transExp(level, breakk, v, tt, el->head);
		if (!ty_match(t.ty, fl->head)){
			EM_error(fun->pos, "unmatched params in function %s\n", S_name(fun->u.call.func));
			return FALSE;
		}
		el = el->tail;
		fl = fl->tail;
	}
	if (el && !fl) {
		EM_error(fun->pos,"too many params in function %s\n", S_name(fun->u.call.func));
		return FALSE;
	} else if (!el && fl) {
		EM_error(fun->pos, "less params in function %s\n", S_name(fun->u.call.func));
		return FALSE;
	} else {
		return TRUE;
	}
}


static bool efields_match(Tr_level level, Tr_exp breakk, S_table v, S_table t, Ty_ty tyy, A_exp e) {
	struct expty et;
	Ty_fieldList ty = tyy->u.record;
	A_efieldList fl = e->u.record.fields;
	while (ty && fl) {
		et = transExp(level, breakk, v, t, fl->head->exp);
		if (!(ty->head->name == fl->head->name) || !ty_match(ty->head->ty, et.ty)){
			EM_error(e->pos, "unmatched name: type in %s", S_name(e->u.record.typ));
			return FALSE;
		}
		ty = ty->tail;
		fl = fl->tail;
	}
	if (ty && !fl) {
		EM_error(e->pos, "less fields in %s", S_name(e->u.record.typ));
		return FALSE;
	} else if (!ty && fl) {
		EM_error(e->pos, "too many field in %s", S_name(e->u.record.typ));
		return FALSE;
	}
	return TRUE;
}

static bool ty_match(Ty_ty type1, Ty_ty type2)
{
	int t1_kind = actual_ty(type1)->kind, t2_kind = actual_ty(type2)->kind;
	return (((t1_kind == Ty_record || t1_kind == Ty_array) && actual_ty(type1) == actual_ty(type2)) ||
		(t1_kind == Ty_record && t2_kind == Ty_nil) ||
		(t2_kind == Ty_record && t1_kind == Ty_nil) ||
		(t1_kind != Ty_record && t1_kind != Ty_array && t1_kind == t2_kind));
}
