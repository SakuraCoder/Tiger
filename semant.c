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
			fieldList = ExpTy.ty->u.record;
			while(fieldList)
			{
				if (fieldList->head->name == v->u.field.sym) 
				{
					Var = Tr_fieldVar(ExpTy.exp, Offset);
					return expTy(Var, actual_ty(fieldList->head->ty));
				}

				fieldList = fieldList->tail;
				Offset++;
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
			Arguments = e->u.call.args; 
			while (Arguments)
			{				
				Tr_expList_prepend(transExp(level, breakk, venv, tenv, Arguments->head).exp, &ArgumentList);
				Arguments = Arguments->tail;
			}
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
				fieldList = e->u.record.fields;
				while (fieldList)
				{
					Tr_expList_prepend(transExp(level, breakk, venv, tenv, fieldList->head->exp).exp, &RecordExpList);
					fieldList = fieldList->tail;
					Offset++;
				}
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
		while (SeqExpList)
		{
			SeqExpTy = transExp(level, breakk, venv, tenv, SeqExpList->head);
			Tr_expList_prepend(SeqExpTy.exp, &Seq_TyList);
			SeqExpList = SeqExpList->tail;
		}

		return expTy(Tr_seqExp(Seq_TyList), SeqExpTy.ty);
	}
	case A_assignExp:
	{
		struct expty assignVar = transVar(level, breakk, venv, tenv, e->u.assign.var);
		struct expty AssignExp = transExp(level, breakk, venv, tenv, e->u.assign.exp);
		/*
		if(e->u.assign.exp->kind == A_ifExp)
		{
			A_exp thenExp = A_AssignExp(e->pos, e->u.assign.var, A_IntExp(e->pos, 1));
			A_exp elseExp = A_AssignExp(e->pos, e->u.assign.var, A_IntExp(e->pos, 0));

			A_exp newtest = A_IfExp(e->pos, e->u.assign.exp, thenExp, elseExp);
			return transExp(level, breakk, v, t, newtest); //single test
		}
		*/
		if (!equal_ty(assignVar.ty, AssignExp.ty)) 
			EM_error(e->pos, "Types of left and right side of assignment do not match!");

		return expTy(Tr_assignExp(assignVar.exp, AssignExp.exp), Ty_Void());
	}
	case A_ifExp:
	{
		struct expty testExpTy, thenExpTy;
		struct expty elseExpTy = { NULL, NULL };
		A_exp test_exp = e->u.iff.test;
		A_exp then_exp = e->u.iff.then;
		A_exp else_exp = e->u.iff.elsee;

		if (test_exp->kind == A_ifExp)
		{
			thenExpTy = transExp(level, breakk, venv, tenv, then_exp);
			if (else_exp)
				elseExpTy = transExp(level, breakk, venv, tenv, else_exp);
			if (test_exp->u.iff.then->kind == A_intExp && test_exp->u.iff.then->u.intt == 1) // or
			{
				struct expty single_test = transExp(level, breakk, venv, tenv, test_exp->u.iff.elsee); //single test
				A_exp newtest = A_IfExp(test_exp->pos, test_exp->u.iff.test, then_exp, else_exp);
				struct expty multi_test = transExp(level, breakk, venv, tenv, newtest); //single test

				return expTy(Tr_ifExp(single_test.exp, thenExpTy.exp, multi_test.exp), thenExpTy.ty);
			}
			else if (test_exp->u.iff.elsee->kind == A_intExp && test_exp->u.iff.elsee->u.intt == 0)
			{
				struct expty single_test = transExp(level, breakk, venv, tenv, test_exp->u.iff.then); //single test
				A_exp newtest = A_IfExp(test_exp->pos, test_exp->u.iff.test, then_exp, else_exp);
				struct expty multi_test = transExp(level, breakk, venv, tenv, newtest); //single test

				return expTy(Tr_ifExp(single_test.exp, multi_test.exp, elseExpTy.exp), elseExpTy.ty);
			}
		}
		else
		{
			Tr_access access = Tr_allocLocal(level, FALSE);	
			Tr_exp tmp = Tr_simpleVar(access, level);
			Tr_exp assing_true = Tr_assignExp(tmp, Tr_intExp(1));
			Tr_exp assing_false = Tr_assignExp(tmp, Tr_intExp(0));

			if (else_exp && then_exp->kind == A_intExp && then_exp->u.intt == 1) // or
			{
				printf("reach1\n");
				testExpTy = transExp(level, breakk, venv, tenv, test_exp); //single test
				thenExpTy = transExp(level, breakk, venv, tenv, then_exp); //single test
				elseExpTy = transExp(level, breakk, venv, tenv, else_exp);

				return expTy(Tr_eseqExp(Tr_ifExp(testExpTy.exp, assing_true, Tr_ifExp(elseExpTy.exp, assing_true, assing_false)), tmp), thenExpTy.ty);
			}
			else if (else_exp && else_exp->kind == A_intExp && else_exp->u.intt == 0)
			{
				printf("reach2\n");
				testExpTy = transExp(level, breakk, venv, tenv, test_exp); //single test
				thenExpTy = transExp(level, breakk, venv, tenv, then_exp); //single test
				elseExpTy = transExp(level, breakk, venv, tenv, else_exp);

				return expTy(Tr_eseqExp(Tr_ifExp(testExpTy.exp, Tr_ifExp(thenExpTy.exp, assing_true, assing_false), assing_false),tmp), elseExpTy.ty);
			}
            printf("reach3\n");
			testExpTy = transExp(level, breakk, venv, tenv, test_exp);
			thenExpTy = transExp(level, breakk, venv, tenv, then_exp);
			if (else_exp)
			{
				elseExpTy = transExp(level, breakk, venv, tenv, else_exp);
				if (testExpTy.ty->kind != Ty_int)
				{
					EM_error(e->u.iff.test->pos, "Test is required to be int type.");
					return expTy(Tr_noExp(), Ty_Void());
				}
			}
			return expTy(Tr_ifExp(testExpTy.exp, thenExpTy.exp, elseExpTy.exp), thenExpTy.ty);
		}

			
	}
	
	case A_whileExp: 
	{
		struct expty whileExpTy = transExp(level, breakk, venv, tenv, e->u.whilee.test);
		if (whileExpTy.ty->kind != Ty_int)
			EM_error(e->pos, "While test should be int type.");
		return expTy(Tr_whileExp(whileExpTy.exp, 
								 transExp(level, Tr_doneExp(), venv, tenv, e->u.whilee.body).exp,
								 Tr_doneExp()),
					 Ty_Void());
	}
	case A_forExp: 
	{
		/*Transform for into while*/
		A_dec i_Dec			= A_VarDec(e->pos, e->u.forr.var,	   NULL, e->u.forr.lo);
		A_dec limit_Dec		= A_VarDec(e->pos, S_Symbol("limit"), NULL, e->u.forr.hi);
		A_dec test_Dec		= A_VarDec(e->pos, S_Symbol("test"),  NULL, A_IntExp(e->pos, 1));
		A_decList for_Dec	= A_DecList(i_Dec, A_DecList(limit_Dec, A_DecList(test_Dec, NULL)));

		A_exp i_Exp			 = A_VarExp(	e->pos, A_SimpleVar(e->pos, e->u.forr.var));
		A_exp then_Exp		 = A_AssignExp(	e->pos, A_SimpleVar(e->pos, e->u.forr.var), A_OpExp(e->pos, A_plusOp, i_Exp, A_IntExp(e->pos, 1)));
		A_exp limit_Exp		 = A_VarExp(	e->pos, A_SimpleVar(e->pos, S_Symbol("limit")));
		A_exp else_Exp		 = A_AssignExp( e->pos, A_SimpleVar(e->pos, S_Symbol("test")), A_IntExp(e->pos, 0));
		A_exp limit_test_Exp = A_IfExp(		e->pos, A_OpExp(	e->pos, A_ltOp, i_Exp, limit_Exp), then_Exp, else_Exp);
		A_exp forSeq_Exp	 = A_SeqExp(	e->pos, A_ExpList(	e->u.forr.body, A_ExpList(limit_test_Exp, NULL)));
		A_exp test_Exp		 = A_VarExp(	e->pos, A_SimpleVar(e->pos, S_Symbol("test")));
		A_exp while_Exp		 = A_WhileExp(	e->pos, test_Exp, forSeq_Exp);
		A_exp if_Exp		 = A_IfExp(		e->pos, A_OpExp(e->pos, A_leOp, e->u.forr.lo, e->u.forr.hi), while_Exp, NULL);
		A_exp ifSeq_Exp		 = A_SeqExp(	e->pos, A_ExpList(if_Exp, NULL));
		A_exp letExp		 = A_LetExp(	e->pos, for_Dec, ifSeq_Exp);
		
		return transExp(level, breakk, venv, tenv, letExp);		
	}
	case A_breakExp:
	{
		if (!breakk) 
			return expTy(Tr_noExp(), Ty_Void());
		else 
			return expTy(Tr_breakExp(breakk), Ty_Void());
	}
	case A_letExp: 
	{
		A_decList decList = e->u.let.decs;
		Tr_expList l = NULL;
		S_beginScope(venv);
		S_beginScope(tenv);

		while (decList)
		{
			Tr_expList_prepend(transDec(level, breakk, venv, tenv, decList->head), &l);
			decList = decList->tail;
		}
		struct expty letBodyExpTy = transExp(level, breakk, venv, tenv, e->u.let.body);
		Tr_expList_prepend(letBodyExpTy.exp, &l);

		S_endScope(venv);
		S_endScope(tenv);

		if (level->parent == NULL)
			Tr_procEntryExit(level, Tr_seqExp(l), Tr_formals(level));

		return expTy(Tr_seqExp(l), letBodyExpTy.ty);
	}
	case A_arrayExp:
	{
		Ty_ty arrayTy = actual_ty(S_look(tenv, e->u.array.typ));
		if (!arrayTy)
		{
			EM_error(e->pos, "Array type \'%s\' is undefined!", S_name(e->u.array.typ));
		}
		else if (arrayTy->kind != Ty_array)
		{
			EM_error(e->pos, "\'%s\' is not a array type!", S_name(e->u.array.typ));
		}
		else
		{
			struct expty sizeExpTy = transExp(level, breakk, venv, tenv, e->u.array.size);
			struct expty initExpTy = transExp(level, breakk, venv, tenv, e->u.array.init);
			if (sizeExpTy.ty->kind != Ty_int)
				EM_error(e->pos, "Array size \'%s\' should be int type!", S_name(e->u.array.typ));
			else if (!equal_ty(initExpTy.ty, arrayTy->u.array))
				EM_error(e->pos, "Array type \'%s\' doesn't match!", S_name(e->u.array.typ));
			else
				return expTy(Tr_arrayExp(sizeExpTy.exp, initExpTy.exp), arrayTy);
		}
		/*return of error*/
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
			//printf("type: %d\n", actual_ty(fun->u.fun.result)->kind);
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
			if(f->body->kind == A_ifExp)
			{
				printf("hello\n");
			}
			fun = S_look(venv, f->name);
			//printf("type: %d\n", actual_ty(fun->u.fun.result)->kind);
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
	bool Record_equal_nil = (a == Ty_nil && b == Ty_record) || (b == Ty_nil  && a == Ty_record);
	bool Record_or_Array_equal = (a == Ty_record || a == Ty_array) && a == b;
	bool Normal_equal = a != Ty_record && b != Ty_array && a == b;

	return Record_equal_nil || Record_or_Array_equal || Normal_equal;
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
