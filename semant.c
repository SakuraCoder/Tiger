/*
	Author: Zhao Zihan & Liu Siyuan
	Reference: Chpt.5.
*/
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

/*constructor for expTy*/
/*Reference: Textbook Page 82*/
struct expty expTy(Tr_exp exp, Ty_ty ty)
{
	struct expty e;
	e.exp = exp;
	e.ty  = ty;
	return e;
}
/*-----------------------------------------------------------------------------------------------------*/
/*recursive function of absyn tree*/
static struct expty transVar(Tr_level level, Tr_exp breakk, S_table venv, S_table tenv, A_var v);
static struct expty transExp(Tr_level level, Tr_exp breakk, S_table venv, S_table tenv, A_exp a);
static		 Tr_exp transDec(Tr_level level, Tr_exp breakk, S_table venv, S_table tenv, A_dec d);
static		  Ty_ty transTy (											  S_table tenv, A_ty  t);
/*-----------------------------------------------------------------------------------------------------*/
/*Functions Within the module*/

/*return real type in Ty_ty in case of Ty_name*/
static Ty_ty actual_ty(Ty_ty ty);
/*match check for arguments in function*/
static bool match_args(Tr_level level, Tr_exp breakk, S_table venv, S_table tenv, A_expList args, Ty_tyList formals, A_exp function);

static Ty_tyList makeFormalTyList(S_table, A_fieldList); /*may use #define*/
static bool ty_match(Ty_ty, Ty_ty);
static bool efields_match(Tr_level, Tr_exp, S_table, S_table, Ty_ty, A_exp); /*may use #define*/
static Ty_fieldList makeFieldTys(S_table, A_fieldList); /*may use #define*/
static U_boolList makeFormals(A_fieldList); /*may use #define*/

F_fragList SEM_transProg(A_exp exp)
{
	struct expty et = transExp(Tr_outermost(), NULL, E_base_venv(), E_base_tenv(), exp);

	return Tr_getResult();
}

static struct expty transVar(Tr_level level, Tr_exp breakk, S_table venv, S_table tenv, A_var v) {
	/*empty*/
	if (!v) 
		return expTy(Tr_noExp(), Ty_Void());

	Tr_exp Var;
	struct expty ExpTy;

	switch (v->kind) 
	{
	/* var id. i.e.: a */
	case A_simpleVar:
	{
		E_enventry Env = S_look(venv, v->u.simple);
		Var = Tr_noExp();

		/*Not found*/
		if (!Env || Env->kind != E_varEntry)
		{
			EM_error(v->pos, "Undefined variable: %s.", S_name(v->u.simple));
			break;
		}
		else
		{
			Var = Tr_simpleVar(Env->u.var.access, level);
			return expTy(Var, actual_ty(Env->u.var.ty));
		}
	}
	/* var record. i.e.: a.b */
	case A_fieldVar:
	{
		ExpTy = transVar(level, breakk, venv, tenv, v->u.field.var);
		Var = Tr_noExp();
		/*Type error*/
		if (ExpTy.ty->kind != Ty_record) 
		{
			EM_error(v->pos, "\'%s\' is not a record type.", S_name(v->u.field.sym));
			break;
		}
		else
		{
			int Offset = 0;
			Ty_fieldList fieldList;
			for (fieldList = ExpTy.ty->u.record; fieldList; fieldList = fieldList->tail, Offset++)
			{
				if (fieldList->head->name == v->u.field.sym) 
				{
					Var = Tr_fieldVar(ExpTy.exp, Offset);
					return expTy(Var, actual_ty(fieldList->head->ty));
				}
			}
			EM_error(v->pos, "Can't find field \'%s\' in record type", S_name(v->u.field.sym));
			break;
		}
	}		
	case A_subscriptVar: /*var array (a[b])*/ 
	{
		struct expty ExpTy_Subscript;
		ExpTy = transVar(level, breakk, venv, tenv, v->u.subscript.var);
		Var = Tr_noExp();
		if (ExpTy.ty->kind != Ty_array)
		{
			EM_error(v->pos, "Not a array type");
			break;
		}
		else
		{
			ExpTy_Subscript = transExp(level, breakk, venv, tenv, v->u.subscript.exp);
			if (ExpTy_Subscript.ty->kind != Ty_int)
			{
				EM_error(v->pos, "Subscript is not int type!");
				break;
			}
			else
			{
				Var = Tr_subscriptVar(ExpTy.exp, ExpTy_Subscript.exp);
				return expTy(Var, actual_ty(ExpTy.ty->u.array));
			}
		}
	}		
	default:
		assert(0);
	}
	/*return when error found*/
	return expTy(Var, Ty_Int());
}
static struct expty transExp(Tr_level level, Tr_exp breakk, S_table venv, S_table tenv, A_exp a){
    /*empty*/
	if (!a) 
		return expTy(Tr_noExp(), Ty_Void());

	Tr_exp Exp = Tr_noExp();

	switch (a->kind) 
	{
	case A_varExp:
		return transVar(level, breakk, venv, tenv, a->u.var);
	/*Basic types*/
	case A_nilExp:
		return expTy(Tr_nilExp(), Ty_Nil());
	case A_intExp:
		return expTy(Tr_intExp(a->u.intt), Ty_Int());
	case A_stringExp:
		return expTy(Tr_stringExp(a->u.stringg), Ty_String());
	case A_callExp: 
	{
		E_enventry FunCall = S_look(venv, a->u.call.func);
		if (!FunCall || FunCall->kind != E_funEntry)
			EM_error(a->pos, "Function %s is undefined!\n", S_name(a->u.call.func));
		else 
		{
			struct expty tempArg;
			A_expList Arguments = NULL;
			Tr_expList ArgumentList = NULL;
			Ty_tyList formalList = FunCall->u.fun.formals;
			for (Arguments = a->u.call.args; Arguments; Arguments = Arguments->tail)
				Tr_expList_prepend(transExp(level, breakk, venv, tenv, Arguments->head).exp, &ArgumentList);

			Exp = Tr_callExp(FunCall->u.fun.label, FunCall->u.fun.level, level, &ArgumentList);						
			Arguments = a->u.call.args;

			while (Arguments && formalList) 
			{
				tempArg = transExp(level, breakk, venv, tenv, Arguments->head);
				if (!ty_match(tempArg.ty, formalList->head))
					EM_error(a->pos, "Function parameters type failed to match in \'%s\'\n", S_name(a->u.call.func));
				Arguments = Arguments->tail;
				formalList = formalList->tail;
			}
			if (Arguments && !formalList)
				EM_error(a->pos, "Function \'%s\' parameter redundant!\n", S_name(a->u.call.func));
			else if (!Arguments && formalList) 
				EM_error(a->pos, "Function \'%s\' parameter insufficient!\n", S_name(a->u.call.func));
			else if(!FunCall->u.fun.result)
				EM_error(a->pos, "Function \'%s\' return type undefined.\n", S_name(a->u.call.func));
			else
				return expTy(Exp, actual_ty(FunCall->u.fun.result));
		}
		return expTy(Exp, Ty_Void());
	}
	case A_opExp: 
	{
		A_oper oper = a->u.op.oper;
		struct expty left = transExp(level, breakk, venv, tenv, a->u.op.left);
		struct expty right = transExp(level, breakk, venv, tenv, a->u.op.right);
		if (0 <= oper && oper < 4) {/* check +,-,*,/ */
			if (left.ty->kind != Ty_int && left.ty->kind != Ty_double) {
				EM_error(a->u.op.left->pos, "int or double required(op)");
			}
			else if (right.ty->kind != Ty_int && right.ty->kind != Ty_double) {
				EM_error(a->u.op.right->pos, "int or double required(op)");
			}
			else if (left.ty->kind == Ty_int && right.ty->kind == Ty_int) {
				return expTy(Tr_arithExp(oper, left.exp, right.exp), Ty_Int());
			}
			else {
				return expTy(Tr_arithExp(oper, left.exp, right.exp), Ty_Double());
			}
			return expTy(Tr_noExp(), Ty_Int());
		}
		else if (3 < oper && oper < 10) {
			Tr_exp translation = Tr_noExp();
			if (oper == 4 || oper == 5) {/*check record type can be nil(=, <>)*/
				switch (left.ty->kind) {
				case Ty_int:
				case Ty_double:/*see is double query like int TODO*/
					if (right.ty->kind == Ty_int || right.ty->kind == Ty_double) translation = Tr_eqExp(oper, left.exp, right.exp);
					else { EM_error(a->u.op.right->pos, "unexpected type in comparsion"); }
					break;
				case Ty_string:
					if (ty_match(right.ty, left.ty)) translation = Tr_eqStringExp(oper, left.exp, right.exp);
					else { EM_error(a->u.op.right->pos, "unexpected type in comparsion"); }
					break;
				case Ty_array:
					if (ty_match(right.ty, left.ty)) translation = Tr_eqRef(oper, left.exp, right.exp);
					else { EM_error(a->u.op.right->pos, "unexpected type in comparsion"); }
					break;
				case Ty_record:
					if (ty_match(right.ty, left.ty) || right.ty->kind == Ty_nil) translation = Tr_eqRef(oper, left.exp, right.exp);
					else { EM_error(a->u.op.right->pos, "unexpected type in comparsion"); }
					break;
				default:
					EM_error(a->u.op.right->pos, "unexpected expression in comparsion");
				}
				return expTy(translation, Ty_Int());
			}
			else {
				switch (left.ty->kind) {
				case Ty_double:
				case Ty_int:
					if (right.ty->kind == Ty_double || right.ty->kind == Ty_int) translation = Tr_relExp(oper, left.exp, right.exp);
					else { EM_error(a->u.op.right->pos, "unexpected type in comparsion"); }
					break;
				case Ty_string:
					if (right.ty->kind == Ty_string) translation = Tr_eqStringExp(oper, left.exp, right.exp);
					else { EM_error(a->u.op.right->pos, "unexpected type in comparsion"); }
					break;
				default:
					EM_error(a->u.op.right->pos, "unexpected type in comparsion");
				}
				return expTy(translation, Ty_Int());
			}
		}
		else {
			assert(0);
		}
	}
	case A_recordExp: {/*record create*/
		Ty_ty recty = actual_ty(S_look(tenv, a->u.record.typ));
	    if (!recty) { /*cant find record-type in table tenv*/ 
			EM_error(a->pos, "undefined type %s (debug recordExp)", S_name(a->u.record.typ)); 
		} else {
			if (recty->kind != Ty_record){
				EM_error(a->pos, "%s is not a record type", S_name(a->u.record.typ));	
				return expTy(Tr_noExp(), Ty_Record(NULL));
			}
			if (efields_match(level, breakk, venv, tenv, recty, a)) {/*check record field is matched*/
				Tr_expList l = NULL;
				int n = 0;
				A_efieldList el;
				for (el = a->u.record.fields; el; el = el->tail, n++) {
					struct expty val = transExp(level, breakk, venv, tenv, el->head->exp);	
					Tr_expList_prepend(val.exp, &l);
				}
				return expTy(Tr_recordExp(n, l), recty);
			}
		}
		return expTy(Tr_noExp(), Ty_Record(NULL));
		}
	case A_seqExp: {
		Tr_expList l = NULL;
		A_expList list = a->u.seq;
		struct expty seqone;
		if (!list) {
			return expTy(Tr_noExp(), Ty_Void());
		}
		for (; list; list = list->tail) {
			seqone = transExp(level, breakk, venv, tenv, list->head);
			Tr_expList_prepend(seqone.exp, &l);
		}
		return expTy(Tr_seqExp(l), seqone.ty);
	}
	case A_assignExp: {
		struct expty final4 = transVar(level, breakk, venv, tenv, a->u.assign.var);
		struct expty final5 = transExp(level, breakk, venv, tenv, a->u.assign.exp);
		if (!ty_match(final4.ty, final5.ty)) {
			EM_error(a->pos, "unmatched assign exp");
		}
		return expTy(Tr_assignExp(final4.exp, final5.exp), Ty_Void());
	}
	case A_ifExp: {
		struct expty final = transExp(level, breakk, venv, tenv, a->u.iff.test);
		struct expty final2 = transExp(level, breakk, venv, tenv, a->u.iff.then);
		struct expty final3 = { NULL, NULL };
		if (a->u.iff.elsee) { /*no else-part*/
			final3 = transExp(level, breakk, venv, tenv, a->u.iff.elsee);
			if (final.ty->kind != Ty_int) {
				EM_error(a->u.iff.test->pos, "int required");
			}
			if (!ty_match(final2.ty, final3.ty)) {
				EM_error(a->pos, "if-else sentence must return same type");
			}
		}
		return expTy(Tr_ifExp(final.exp, final2.exp, final3.exp), final2.ty);
	}
	case A_whileExp: {
		struct expty final = transExp(level, breakk, venv, tenv, a->u.whilee.test);
		if (final.ty->kind != Ty_int) {
			EM_error(a->pos, "int required");
		}
		Tr_exp done = Tr_doneExp();
		struct expty body = transExp(level, done, venv, tenv, a->u.whilee.body);
		return expTy(Tr_whileExp(final.exp, body.exp, done), Ty_Void());
	}
	case A_forExp: {
		EM_error(a->pos, "\nsome one said for is better than while\nmake them unhappy \nahahaha");
		return expTy(Tr_noExp(), Ty_Int());
	}
	case A_breakExp:
		if (!breakk) return expTy(Tr_noExp(), Ty_Void());
		return expTy(Tr_breakExp(breakk), Ty_Void());
	case A_letExp: {
		A_decList decs;
		Tr_expList l = NULL;
		S_beginScope(venv);
		S_beginScope(tenv);
		for (decs = a->u.let.decs; decs; decs = decs->tail) {
			Tr_expList_prepend(transDec(level, breakk, venv, tenv, decs->head), &l);
		}
		struct expty final = transExp(level, breakk, venv, tenv, a->u.let.body);
		Tr_expList_prepend(final.exp, &l);
		S_endScope(venv);
		S_endScope(tenv);
		if (level->parent == NULL) // 是否在最外层
			Tr_procEntryExit(level, Tr_seqExp(l), Tr_formals(level));
		return expTy(Tr_seqExp(l), final.ty);
	}
	case A_arrayExp: {/*array create*/
		Ty_ty arrayty = actual_ty(S_look(tenv, a->u.array.typ));
		if (!arrayty) {
			EM_error(a->pos, "undeined array type %s", S_name(a->u.array.typ));
			return expTy(Tr_noExp(), Ty_Int());
		}
		if (arrayty->kind != Ty_array) {
			EM_error(a->pos, "%s is not a array type", S_name(a->u.array.typ));
			return expTy(Tr_noExp(), Ty_Int());
		}
	    struct expty final2 = transExp(level, breakk, venv, tenv, a->u.array.size);
		struct expty final3 = transExp(level, breakk, venv, tenv, a->u.array.init);
		if (final2.ty->kind != Ty_int) {
			EM_error(a->pos, "array size should be int %s", S_name(a->u.array.typ));
		} else if (!ty_match(final3.ty, arrayty->u.array)){
			EM_error(a->pos, "unmatched array type in %s", S_name(a->u.array.typ));
		} else {	
			return expTy(Tr_arrayExp(final2.exp, final3.exp), arrayty);
		}
		return expTy(Tr_noExp(), Ty_Int());
	}
	default:
		assert(0);
	}
}
static		 Tr_exp transDec(Tr_level level, Tr_exp breakk, S_table venv, S_table tenv, A_dec d) {
	
	struct expty final;
	A_fundec f;
	Ty_ty resTy, namety, isname;
	Ty_tyList formalTys, s;
	A_fieldList l;
	A_nametyList nl;
	A_fundecList fcl;
	E_enventry fun;
	int iscyl, isset;
	Tr_access ac;

	switch (d->kind) {
	case A_varDec:
		final = transExp(level, breakk, venv, tenv, d->u.var.init);
		ac = Tr_allocLocal(level, d->u.var.escape);	
		if (!d->u.var.typ) {/*unpoint type*/
			if (final.ty->kind == Ty_nil || final.ty->kind == Ty_void) {
				/*why keep void type ???*/
				EM_error(d->pos, "init should not be nil without type in %s", S_name(d->u.var.var));
				S_enter(venv, d->u.var.var, E_VarEntry(ac, Ty_Int()));
			} else {
				S_enter(venv, d->u.var.var, E_VarEntry(ac, final.ty));
			}
		} else {
			resTy = S_look(tenv, d->u.var.typ);
			if (!resTy) {
				EM_error(d->pos, "undifined type %s", S_name(d->u.var.typ));
			} else {
				if (!ty_match(resTy, final.ty)) {
					EM_error(d->pos, "unmatched type in %s", S_name(d->u.var.typ));
					S_enter(venv, d->u.var.var, E_VarEntry(ac, resTy));
				} else {
					S_enter(venv, d->u.var.var, E_VarEntry(ac, resTy));
				}
			}
		}
		return Tr_assignExp(Tr_simpleVar(ac, level), final.exp);
	case A_functionDec:
		for (fcl = d->u.function; fcl; fcl = fcl->tail) {
			if (fcl->head->result) {/*check return type is exist*/
				resTy = S_look(tenv, fcl->head->result);
				if (!resTy) {
					EM_error(fcl->head->pos, "undefined type for return type");
					resTy = Ty_Void();
				} 
			} else {
				resTy = Ty_Void();
			}
			/*add func-info to venv*/
			formalTys = makeFormalTyList(tenv, fcl->head->params);
			{
			Temp_label funLabel = Temp_newlabel();
			Tr_level l = Tr_newLevel(level, funLabel, makeFormals(fcl->head->params));/* create a new level */
			S_enter(venv, fcl->head->name, E_FunEntry(l, funLabel, formalTys, resTy));
			}
		}
		/*deal func-body-exp*/
		for (fcl = d->u.function; fcl; fcl = fcl->tail) {
			f = fcl->head;
			E_enventry funEntry = S_look(venv, f->name); /*get fun-info*/
			S_beginScope(venv);
			formalTys = funEntry->u.fun.formals;/*Ty-list should get from venv*/
			/*add params-name to venv*/
			Tr_accessList acls = Tr_formals(funEntry->u.fun.level);
			for (l = f->params, s = formalTys; l && s && acls; l = l->tail, s = s->tail, acls = acls->tail) {
				S_enter(venv, l->head->name, E_VarEntry(acls->head, s->head));
			}
			final = transExp(funEntry->u.fun.level, breakk, venv, tenv, f->body);
			fun = S_look(venv, f->name);
			if (!ty_match(fun->u.fun.result, final.ty)) {/*check return type is match body type*/
				EM_error(f->pos, "incorrect return type in function '%s'", S_name(f->name));
			}
			Tr_procEntryExit(funEntry->u.fun.level, final.exp, acls);
			S_endScope(venv);
		}
		return Tr_noExp();
	case A_typeDec:
		for (nl = d->u.type; nl; nl = nl->tail) {
			S_enter(tenv, nl->head->name, Ty_Name(nl->head->name,NULL));
		} /* add name to tenv, Ty_ty set NULL*/
		iscyl = TRUE;
		for (nl = d->u.type; nl; nl = nl->tail) {
			resTy = transTy(tenv, nl->head->ty);
			if (iscyl) {
				if (resTy->kind != Ty_name) {
					iscyl = FALSE;
				}
			}
			if (!nl->tail && resTy->kind != Ty_name && isset) {
				/*line num is some bug*/
				EM_error(d->pos,"warning: actual type should declare brefore nameTy type");
			}
			namety = S_look(tenv, nl->head->name);
			namety->u.name.ty = resTy;
		}
		if (iscyl) EM_error(d->pos,"illegal type cycle: cycle must contain record, array");
		return Tr_noExp();
	default:
		assert(0);
	}
}

static		  Ty_ty transTy (											  S_table tenv, A_ty  t) {
	Ty_ty final = NULL;
	Ty_fieldList fieldTys;

	switch (t->kind) {
	case A_nameTy:
		final = S_look(tenv, t->u.name);
		if (!final) {
			EM_error(t->pos, "undefined type %s", S_name(t->u.name));
			return Ty_Int();
		}
		return final;
	case A_recordTy:
		fieldTys = makeFieldTys(tenv, t->u.record);
		return Ty_Record(fieldTys);
	case A_arrayTy:
		final = S_look(tenv, t->u.array);
		if (!final) EM_error(t->pos, "undefined type %s", S_name(t->u.array));
		return Ty_Array(final);
	default:
		assert(0);
	}
}

/*Reference Textbook Page 83*/
static Ty_ty actual_ty(Ty_ty ty) 
{
	if (ty && ty->kind == Ty_name)
		actual_ty(ty->u.name.ty);
	else return ty;
}














static U_boolList makeFormals(A_fieldList params) {
	/* HACK (short escape-var judge) default all escape-var */
	U_boolList head = NULL, tail = NULL;
	A_fieldList p = params;
	for (; p; p = p->tail) {
		if (head) {
			tail->tail = U_BoolList(TRUE, NULL);
			tail = tail->tail;
		} else {
			head = U_BoolList(TRUE, NULL);
			tail = head;
		}
	}
	return head;
}

static Ty_fieldList makeFieldTys(S_table t, A_fieldList fs) {
	A_fieldList f;
	Ty_fieldList tys = NULL, head;
	Ty_ty ty;
	Ty_field tmp;

	for (f = fs; f; f = f->tail) {
		ty = S_look(t, f->head->typ);
		if (!ty) {
			EM_error(f->head->pos, "undefined type %s", S_name(f->head->typ));
		} else {
		tmp = Ty_Field(f->head->name, ty);
		if (tys) {
			tys->tail = Ty_FieldList(tmp, NULL);
			tys = tys->tail;
		} else {
			tys = Ty_FieldList(tmp, NULL);
			head = tys;
		}

		}
	}
	return head;
}

static Ty_tyList makeFormalTyList(S_table t, A_fieldList fl) {
	Ty_tyList final = NULL, head = final;
	A_fieldList l = fl;
	Ty_ty ty;

	for (; l; l = l->tail) {
		ty = S_look(t, l->head->typ);
		if(!ty) {
			EM_error(l->head->pos, "undefined type %s", S_name(l->head->typ));
			ty = Ty_Int();
		}
		if (!final) {
			final = Ty_TyList(ty, NULL);
			head = final;
		} else {
			final->tail = Ty_TyList(ty, NULL);
			final = final->tail;
		}
	}
	return head;
}

static bool ty_match(Ty_ty tt, Ty_ty ee) {
	Ty_ty t = actual_ty(tt);
	Ty_ty e = actual_ty(ee);
	int tk = t->kind;
	int ek = e->kind;

	return (((tk == Ty_record || tk == Ty_array) && t == e) ||
			 (tk == Ty_record && ek == Ty_nil) ||
			 (ek == Ty_record && tk == Ty_nil) ||
			 (tk != Ty_record && tk != Ty_array && tk == ek));
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
