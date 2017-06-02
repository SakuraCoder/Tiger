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

/*-----------------------------------------------------------------------------------------------------*/
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
static struct expty transExp(Tr_level level, Tr_exp breakk, S_table venv, S_table tenv, A_exp e);
static		 Tr_exp transDec(Tr_level level, Tr_exp breakk, S_table venv, S_table tenv, A_dec d);
static		  Ty_ty transTy (											  S_table tenv, A_ty  t);
/*-----------------------------------------------------------------------------------------------------*/
/*Functions Within the module*/

/*return real type in Ty_ty in case of Ty_name*/
static Ty_ty actual_ty(Ty_ty ty);
/*match check for two Ty_ty type*/
static bool equal_ty(Ty_ty ty_a, Ty_ty ty_b);


static Ty_tyList makeFormalTyList(S_table, A_fieldList); /*may use #define*/
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
			EM_error(v->pos, "Undefined variable: \'%s\'.", S_name(v->u.simple));
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
static struct expty transExp(Tr_level level, Tr_exp breakk, S_table venv, S_table tenv, A_exp e){
    /*empty*/
	if (!e) 
		return expTy(Tr_noExp(), Ty_Void());

	Tr_exp Exp = Tr_noExp();

	switch (e->kind) 
	{
	case A_varExp:
		return transVar(level, breakk, venv, tenv, e->u.var);
	case A_nilExp:
		return expTy(Tr_nilExp(), Ty_Nil());
	case A_intExp:
		return expTy(Tr_intExp(e->u.intt), Ty_Int());
	case A_stringExp:
		return expTy(Tr_stringExp(e->u.stringg), Ty_String());
	case A_callExp: 
	{
		E_enventry FunCall = S_look(venv, e->u.call.func);
		if (!FunCall || FunCall->kind != E_funEntry)
			EM_error(e->pos, "Function \'%s\' is undefined!\n", S_name(e->u.call.func));
		else 
		{
			struct expty tempArg;
			A_expList Arguments = NULL;
			Tr_expList ArgumentList = NULL;
			Ty_tyList formalList = FunCall->u.fun.formals;
			for (Arguments = e->u.call.args; Arguments; Arguments = Arguments->tail)
				Tr_expList_prepend(transExp(level, breakk, venv, tenv, Arguments->head).exp, &ArgumentList);

			Exp = Tr_callExp(FunCall->u.fun.label, FunCall->u.fun.level, level, &ArgumentList);						
			Arguments = e->u.call.args;

			while (Arguments && formalList) 
			{
				tempArg = transExp(level, breakk, venv, tenv, Arguments->head);
				if (!equal_ty(tempArg.ty, formalList->head)) 
				{
					EM_error(e->pos, "Function parameters type failed to match in \'%s\'\n", S_name(e->u.call.func));
					return expTy(Exp, Ty_Void());
				}
				Arguments = Arguments->tail;
				formalList = formalList->tail;
			}
			if (Arguments && !formalList)
				EM_error(e->pos, "Function \'%s\' parameter redundant!\n", S_name(e->u.call.func));
			else if (!Arguments && formalList) 
				EM_error(e->pos, "Function \'%s\' parameter insufficient!\n", S_name(e->u.call.func));
			else if(!FunCall->u.fun.result)
				EM_error(e->pos, "Function \'%s\' return type undefined.\n", S_name(e->u.call.func));
			else
				return expTy(Exp, actual_ty(FunCall->u.fun.result));
		}
		return expTy(Exp, Ty_Void());
	}
	case A_opExp: 
	{
		struct expty leftExp = transExp(level, breakk, venv, tenv, e->u.op.left);
		struct expty rightExp = transExp(level, breakk, venv, tenv, e->u.op.right);
		Tr_exp OpExp = Tr_noExp();
		switch (e->u.op.oper)
		{
		case A_plusOp:
		case A_minusOp:
		case A_timesOp:
		case A_divideOp:
		{
			if (leftExp.ty->kind != Ty_int) 
				EM_error(e->u.op.left->pos, "Left hand side is not int type!");
			else if (rightExp.ty->kind != Ty_int) 
				EM_error(e->u.op.right->pos, "Right hand side is not int type!");
			else if (leftExp.ty->kind == Ty_int && rightExp.ty->kind == Ty_int) 
				OpExp = Tr_arithExp(e->u.op.oper, leftExp.exp, rightExp.exp);
			break;
		}
		case A_eqOp: 
		case A_neqOp: 
		{
			switch (leftExp.ty->kind) 
			{
			case Ty_int:
			case Ty_string:
			{
				if (!equal_ty(rightExp.ty, leftExp.ty))
					EM_error(e->u.op.right->pos, "Left and right hand side types do not match.");
				else
					OpExp = Tr_eqStringExp(e->u.op.oper, leftExp.exp, rightExp.exp);
				break;
			}
				
			case Ty_array:
			{
				if (!equal_ty(rightExp.ty, leftExp.ty))
					EM_error(e->u.op.right->pos, "Left and right hand side types do not match.");
				else
					OpExp = Tr_eqRef(e->u.op.oper, leftExp.exp, rightExp.exp);
				break;
			}
			case Ty_record:
			{
				if (!equal_ty(rightExp.ty, leftExp.ty))
					EM_error(e->u.op.right->pos, "Left and right hand side types do not match.");
				else if (equal_ty(rightExp.ty, leftExp.ty) || rightExp.ty->kind == Ty_nil)
					OpExp = Tr_eqRef(e->u.op.oper, leftExp.exp, rightExp.exp);
				break;
			}
			default:
				EM_error(e->u.op.right->pos, "Unexpected type of left hand side.");
			}
			break;
			
		}
		case A_ltOp: 
		case A_leOp:
		case A_gtOp:
		case A_geOp:
		{
			switch (leftExp.ty->kind)
			{
			case Ty_int:
			{
				if (!rightExp.ty->kind == Ty_int)
					EM_error(e->u.op.right->pos, "Right hand side type is expected to be int.");
				else
					OpExp = Tr_relExp(e->u.op.oper, leftExp.exp, rightExp.exp);
				break;
			}
			case Ty_string:
			{
				if (!rightExp.ty->kind == Ty_string)
					EM_error(e->u.op.right->pos, "Right hand side type is expected to be string.");
				else
					OpExp = Tr_eqStringExp(e->u.op.oper, leftExp.exp, rightExp.exp);
				break;
			}
			default:
				EM_error(e->u.op.right->pos, "Unexpected type of left hand side.");
			}
			break;
		}
		default:
			assert(0);
		}
		return expTy(OpExp, Ty_Int());
	}
	case A_recordExp:
	{
		Ty_ty recordTy = actual_ty(S_look(tenv, e->u.record.typ));

	    if (!recordTy)
			EM_error(e->pos, "Undefined record type \'%s.\'", S_name(e->u.record.typ)); 
		else if (recordTy->kind != Ty_record)
			EM_error(e->pos, "\'%s.\' is not a record type!", S_name(e->u.record.typ));
		else
		{
			struct expty RecordExp;
			Ty_fieldList tyList = recordTy->u.record;
			A_efieldList fieldList = e->u.record.fields;
			while (tyList && fieldList) 
			{
				RecordExp = transExp(level, breakk, venv, tenv, fieldList->head->exp);
				if (!equal_ty(tyList->head->ty, RecordExp.ty) || tyList->head->name != fieldList->head->name)
				{
					EM_error(e->pos, "Type of \'%s\' in record does not match definition.", S_name(e->u.record.typ));
					return expTy(Tr_noExp(), Ty_Record(NULL));
				}
				tyList = tyList->tail;
				fieldList = fieldList->tail;
			}
			if (tyList && !fieldList) 
				EM_error(e->pos, "Fields insufficient in \'%s\'.", S_name(e->u.record.typ));
			else if (!tyList && fieldList) 
				EM_error(e->pos, "Fields redundant in \'%s\'.", S_name(e->u.record.typ));
			else
			{
				Tr_expList RecordExpList = NULL;
				int Offset = 0;
				fieldList = e->u.record.fields;
				for (fieldList = e->u.record.fields; fieldList; fieldList = fieldList->tail, Offset++)
					Tr_expList_prepend(transExp(level, breakk, venv, tenv, fieldList->head->exp).exp, &RecordExpList);
				return expTy(Tr_recordExp(Offset, RecordExpList), recordTy);
			}
		}
		/*return of error*/
		return expTy(Tr_noExp(), Ty_Record(NULL));
	}
	case A_seqExp: 
	{
		struct expty SeqExpTy;
		Tr_expList Seq_TyList = NULL;
		A_expList SeqExpList = e->u.seq;
		/*Void sequence*/
		if (!SeqExpList)
			return expTy(Tr_noExp(), Ty_Void());
		for (; SeqExpList; SeqExpList = SeqExpList->tail)
		{
			SeqExpTy = transExp(level, breakk, venv, tenv, SeqExpList->head);
			Tr_expList_prepend(SeqExpTy.exp, &Seq_TyList);
		}
		return expTy(Tr_seqExp(Seq_TyList), SeqExpTy.ty);
	}
	case A_assignExp:
	{
		struct expty assignVar = transVar(level, breakk, venv, tenv, e->u.assign.var);
		struct expty AssignExp = transExp(level, breakk, venv, tenv, e->u.assign.exp);
		if (!equal_ty(assignVar.ty, AssignExp.ty)) 
			EM_error(e->pos, "Types of left and right side of assignment do not match!");
		return expTy(Tr_assignExp(assignVar.exp, AssignExp.exp), Ty_Void());
	}
	case A_ifExp: 
	{
		struct expty final, final2;
		struct expty final3 = { NULL, NULL };
		A_exp test_exp = e->u.iff.test;
		A_exp then_exp = e->u.iff.then;
		A_exp else_exp = e->u.iff.elsee;

		if (test_exp->kind == A_ifExp)
		{
			final2 = transExp(level, breakk, venv, tenv, then_exp);
			if (else_exp)
			{
				final3 = transExp(level, breakk, venv, tenv, else_exp);
			}

			if (test_exp->u.iff.then->kind == A_intExp && test_exp->u.iff.then->u.intt == 1) // or
			{
				struct expty single_test = transExp(level, breakk, venv, tenv, test_exp->u.iff.elsee); //single test
				A_exp newtest = A_IfExp(test_exp->pos, test_exp->u.iff.test, then_exp, else_exp);
				struct expty multi_test = transExp(level, breakk, venv, tenv, newtest); //single test

				return expTy(Tr_ifExp(single_test.exp, final2.exp, multi_test.exp), final2.ty);
			}
			else if (test_exp->u.iff.elsee->kind == A_intExp && test_exp->u.iff.elsee->u.intt == 0)
			{
				struct expty single_test = transExp(level, breakk, venv, tenv, test_exp->u.iff.then); //single test
				A_exp newtest = A_IfExp(test_exp->pos, test_exp->u.iff.test, then_exp, else_exp);
				struct expty multi_test = transExp(level, breakk, venv, tenv, newtest); //single test

				return expTy(Tr_ifExp(single_test.exp, multi_test.exp, final3.exp), final3.ty);
			}
		}
		else
		{
			final = transExp(level, breakk, venv, tenv, test_exp);
			final2 = transExp(level, breakk, venv, tenv, then_exp);
			if (else_exp)
			{
				final3 = transExp(level, breakk, venv, tenv, else_exp);

				if (final.ty->kind != Ty_int) {
					EM_error(e->u.iff.test->pos, "int required");
				}
			}
			return expTy(Tr_ifExp(final.exp, final2.exp, final3.exp), final2.ty);
		}
	}
	case A_whileExp: {
		struct expty final = transExp(level, breakk, venv, tenv, e->u.whilee.test);
		if (final.ty->kind != Ty_int) {
			EM_error(e->pos, "int required");
		}
		Tr_exp done = Tr_doneExp();
		struct expty body = transExp(level, done, venv, tenv, e->u.whilee.body);
		return expTy(Tr_whileExp(final.exp, body.exp, done), Ty_Void());
	}
	case A_forExp: {

		A_dec i = A_VarDec(e->pos, e->u.forr.var, NULL, e->u.forr.lo);
		A_dec limit = A_VarDec(e->pos, S_Symbol("limit"), NULL, e->u.forr.hi);
		A_dec test = A_VarDec(e->pos, S_Symbol("test"), NULL, A_IntExp(e->pos, 1));
		A_exp testExp = A_VarExp(e->pos, A_SimpleVar(e->pos, S_Symbol("test")));
		A_exp iExp = A_VarExp(e->pos, A_SimpleVar(e->pos, e->u.forr.var));
		A_exp limitExp = A_VarExp(e->pos, A_SimpleVar(e->pos, S_Symbol("limit")));
		A_exp increment = A_AssignExp(e->pos,
			A_SimpleVar(e->pos, e->u.forr.var),
			A_OpExp(e->pos, A_plusOp, iExp, A_IntExp(e->pos, 1)));
		A_exp setFalse = A_AssignExp(e->pos,
			A_SimpleVar(e->pos, S_Symbol("test")), A_IntExp(e->pos, 0));
		/* The let expression we pass to this function */
		A_exp letExp = A_LetExp(e->pos,
			A_DecList(i, A_DecList(limit, A_DecList(test, NULL))),
			A_SeqExp(e->pos,
				A_ExpList(
					A_IfExp(e->pos,
						A_OpExp(e->pos, A_leOp, e->u.forr.lo, e->u.forr.hi),
						A_WhileExp(e->pos, testExp,
							A_SeqExp(e->pos,
								A_ExpList(e->u.forr.body,
									A_ExpList(
										A_IfExp(e->pos,
											A_OpExp(e->pos, A_ltOp, iExp,
												limitExp),
											increment, setFalse),
										NULL)))),
						NULL),
					NULL)));
		return transExp(level, breakk, venv, tenv, letExp);
	}
	case A_breakExp:
		if (!breakk) return expTy(Tr_noExp(), Ty_Void());
		return expTy(Tr_breakExp(breakk), Ty_Void());	
	case A_letExp: {
		A_decList decs;
		Tr_expList l = NULL;
		S_beginScope(venv);
		S_beginScope(tenv);
		for (decs = e->u.let.decs; decs; decs = decs->tail) {
			Tr_expList_prepend(transDec(level, breakk, venv, tenv, decs->head), &l);
		}
		struct expty final = transExp(level, breakk, venv, tenv, e->u.let.body);
		Tr_expList_prepend(final.exp, &l);
		S_endScope(venv);
		S_endScope(tenv);
		if (level->parent == NULL) // 是否在最外层
			Tr_procEntryExit(level, Tr_seqExp(l), Tr_formals(level));
		return expTy(Tr_seqExp(l), final.ty);
	}
	case A_arrayExp: {/*array create*/
		Ty_ty arrayty = actual_ty(S_look(tenv, e->u.array.typ));
		if (!arrayty) {
			EM_error(e->pos, "undeined array type \'%s\'", S_name(e->u.array.typ));
			return expTy(Tr_noExp(), Ty_Int());
		}
		if (arrayty->kind != Ty_array) {
			EM_error(e->pos, "\'%s\' is not a array type", S_name(e->u.array.typ));
			return expTy(Tr_noExp(), Ty_Int());
		}
	    struct expty final2 = transExp(level, breakk, venv, tenv, e->u.array.size);
		struct expty final3 = transExp(level, breakk, venv, tenv, e->u.array.init);
		if (final2.ty->kind != Ty_int) {
			EM_error(e->pos, "array size should be int \'%s\'", S_name(e->u.array.typ));
		} else if (!equal_ty(final3.ty, arrayty->u.array)){
			EM_error(e->pos, "unmatched array type in \'%s\'", S_name(e->u.array.typ));
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
				EM_error(d->pos, "init should not be nil without type in \'%s\'", S_name(d->u.var.var));
				S_enter(venv, d->u.var.var, E_VarEntry(ac, Ty_Int()));
			} else {
				S_enter(venv, d->u.var.var, E_VarEntry(ac, final.ty));
			}
		} else {
			resTy = S_look(tenv, d->u.var.typ);
			if (!resTy) {
				EM_error(d->pos, "undifined type \'%s\'", S_name(d->u.var.typ));
			} else {
				if (!equal_ty(resTy, final.ty)) {
					EM_error(d->pos, "unmatched type in \'%s\'", S_name(d->u.var.typ));
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
			if (!equal_ty(fun->u.fun.result, final.ty)) {/*check return type is match body type*/
				EM_error(f->pos, "incorrect return type in function '\'%s\''", S_name(f->name));
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
			EM_error(t->pos, "undefined type \'%s\'", S_name(t->u.name));
			return Ty_Int();
		}
		return final;
	case A_recordTy:
		fieldTys = makeFieldTys(tenv, t->u.record);
		return Ty_Record(fieldTys);
	case A_arrayTy:
		final = S_look(tenv, t->u.array);
		if (!final) EM_error(t->pos, "undefined type \'%s\'", S_name(t->u.array));
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
static bool equal_ty(Ty_ty ty_a, Ty_ty ty_b)
{
	int a = actual_ty(ty_a)->kind;
	int b = actual_ty(ty_b)->kind;

	return ((a == Ty_nil && b == Ty_record) || (b == Ty_nil  && a == Ty_record)
		|| ((a == Ty_record || a == Ty_array) && a == b)
		|| (a != Ty_record && b != Ty_array && a == b));
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
			EM_error(f->head->pos, "undefined type \'%s\'", S_name(f->head->typ));
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
			EM_error(l->head->pos, "undefined type \'%s\'", S_name(l->head->typ));
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
