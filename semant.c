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
	e.ty = ty;
	return e;
}
/*-----------------------------------------------------------------------------------------------------*/
/*recursive function of absyn tree*/
static struct expty transVar(Tr_level level, Tr_exp breakk, S_table venv, S_table tenv, A_var v);
static struct expty transExp(Tr_level level, Tr_exp breakk, S_table venv, S_table tenv, A_exp e);
static		 Tr_exp transDec(Tr_level level, Tr_exp breakk, S_table venv, S_table tenv, A_dec d);
static		  Ty_ty transTy(											  S_table tenv, A_ty  t);
/*-----------------------------------------------------------------------------------------------------*/
/*Functions Within the module*/

/*return real type in Ty_ty in case of Ty_name*/
/*Reference Textbook Page 83*/
static Ty_ty actual_ty(Ty_ty ty)
{
	if (ty && ty->kind == Ty_name)
		return actual_ty(ty->u.name.ty);
	else return ty;
}
/*match check for two Ty_ty type*/
static bool equal_ty(Ty_ty ty_a, Ty_ty ty_b)
{
	int a = actual_ty(ty_a)->kind;
	int b = actual_ty(ty_b)->kind;
	bool Record_equal_nil = (a == Ty_nil && b == Ty_record) || (b == Ty_nil  && a == Ty_record);
	bool Record_or_Array_equal = (a == Ty_record || a == Ty_array) && a == b;
	bool Normal_equal = a != Ty_record && b != Ty_array && a == b;

	return Record_equal_nil || Record_or_Array_equal || Normal_equal;
}

/*-----------------------------------------------------------------------------------------------------*/

F_fragList SEM_transProg(A_exp exp)
{
	struct expty et = transExp(Tr_outermost(), NULL, E_base_venv(), E_base_tenv(), exp);

	return Tr_getResult();
}

static struct expty transVar(Tr_level level, Tr_exp breakk, S_table venv, S_table tenv, A_var v) {
	/*empty*/
	if (!v)
		return expTy(Tr_noExp(), Ty_Void());
	else
	{
		Tr_exp Var = Tr_noExp();
		struct expty ExpTy;

		switch (v->kind)
		{
		case A_simpleVar:
		{
			E_enventry Env = S_look(venv, v->u.simple);

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
		case A_fieldVar:
		{
			ExpTy = transVar(level, breakk, venv, tenv, v->u.field.var);

			/*Type error*/
			if (ExpTy.ty->kind != Ty_record)
			{
				EM_error(v->pos, "\'%s\' is not a record type.", S_name(v->u.field.var->u.simple));
				break;
			}
			else
			{
				int Offset = 0;
				Ty_fieldList fieldList;
				fieldList = ExpTy.ty->u.record;
				while (fieldList)
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
		case A_subscriptVar:
		{
			struct expty ExpTy_Subscript;
			ExpTy = transVar(level, breakk, venv, tenv, v->u.subscript.var);

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
		return expTy(Tr_noExp(), Ty_Int());
	}	
}
static struct expty transExp(Tr_level level, Tr_exp breakk, S_table venv, S_table tenv, A_exp e) {
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
				Tr_add_exp(transExp(level, breakk, venv, tenv, Arguments->head).exp, &ArgumentList);
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
			else if (!FunCall->u.fun.result)
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
				OpExp = Tr_binOp(e->u.op.oper, leftExp.exp, rightExp.exp);
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
					OpExp = Tr_stringCmpExp(e->u.op.oper, leftExp.exp, rightExp.exp);
				break;
			}

			case Ty_array:
			{
				if (!equal_ty(rightExp.ty, leftExp.ty))
					EM_error(e->u.op.right->pos, "Left and right hand side types do not match.");
				else
					OpExp = Tr_comOpExp(e->u.op.oper, leftExp.exp, rightExp.exp);
				break;
			}
			case Ty_record:
			{
				if (!equal_ty(rightExp.ty, leftExp.ty))
					EM_error(e->u.op.right->pos, "Left and right hand side types do not match.");
				else if (equal_ty(rightExp.ty, leftExp.ty) || rightExp.ty->kind == Ty_nil)
					OpExp = Tr_comOpExp(e->u.op.oper, leftExp.exp, rightExp.exp);
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
					OpExp = Tr_comOpExp(e->u.op.oper, leftExp.exp, rightExp.exp);
				break;
			}
			case Ty_string:
			{
				if (!rightExp.ty->kind == Ty_string)
					EM_error(e->u.op.right->pos, "Right hand side type is expected to be string.");
				else
					OpExp = Tr_stringCmpExp(e->u.op.oper, leftExp.exp, rightExp.exp);
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
					Tr_add_exp(transExp(level, breakk, venv, tenv, fieldList->head->exp).exp, &RecordExpList);
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
			Tr_add_exp(SeqExpTy.exp, &Seq_TyList);
			SeqExpList = SeqExpList->tail;
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
				testExpTy = transExp(level, breakk, venv, tenv, test_exp); //single test
				thenExpTy = transExp(level, breakk, venv, tenv, then_exp); //single test
				elseExpTy = transExp(level, breakk, venv, tenv, else_exp);

				return expTy(Tr_eseqExp(Tr_ifExp(testExpTy.exp, assing_true, Tr_ifExp(elseExpTy.exp, assing_true, assing_false)), tmp), thenExpTy.ty);
			}
			else if (else_exp && else_exp->kind == A_intExp && else_exp->u.intt == 0)
			{
				testExpTy = transExp(level, breakk, venv, tenv, test_exp); //single test
				thenExpTy = transExp(level, breakk, venv, tenv, then_exp); //single test
				elseExpTy = transExp(level, breakk, venv, tenv, else_exp);

				return expTy(Tr_eseqExp(Tr_ifExp(testExpTy.exp, Tr_ifExp(thenExpTy.exp, assing_true, assing_false), assing_false), tmp), elseExpTy.ty);
			}
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
		A_dec		i_Dec = A_VarDec(e->pos, e->u.forr.var, NULL, e->u.forr.lo);
		A_dec	limit_Dec = A_VarDec(e->pos, S_Symbol("limit"), NULL, e->u.forr.hi);
		A_dec	 test_Dec = A_VarDec(e->pos, S_Symbol("test"), NULL, A_IntExp(e->pos, 1));
		A_decList for_Dec = A_DecList(i_Dec, A_DecList(limit_Dec, A_DecList(test_Dec, NULL)));

		A_exp i_Exp = A_VarExp(e->pos, A_SimpleVar(e->pos, e->u.forr.var));
		A_exp then_Exp = A_AssignExp(e->pos, A_SimpleVar(e->pos, e->u.forr.var), A_OpExp(e->pos, A_plusOp, i_Exp, A_IntExp(e->pos, 1)));
		A_exp limit_Exp = A_VarExp(e->pos, A_SimpleVar(e->pos, S_Symbol("limit")));
		A_exp else_Exp = A_AssignExp(e->pos, A_SimpleVar(e->pos, S_Symbol("test")), A_IntExp(e->pos, 0));
		A_exp limit_test_Exp = A_IfExp(e->pos, A_OpExp(e->pos, A_ltOp, i_Exp, limit_Exp), then_Exp, else_Exp);
		A_exp forSeq_Exp = A_SeqExp(e->pos, A_ExpList(e->u.forr.body, A_ExpList(limit_test_Exp, NULL)));
		A_exp test_Exp = A_VarExp(e->pos, A_SimpleVar(e->pos, S_Symbol("test")));
		A_exp while_Exp = A_WhileExp(e->pos, test_Exp, forSeq_Exp);
		A_exp if_Exp = A_IfExp(e->pos, A_OpExp(e->pos, A_leOp, e->u.forr.lo, e->u.forr.hi), while_Exp, NULL);
		A_exp ifSeq_Exp = A_SeqExp(e->pos, A_ExpList(if_Exp, NULL));
		A_exp let_Exp = A_LetExp(e->pos, for_Dec, ifSeq_Exp);

		return transExp(level, breakk, venv, tenv, let_Exp);
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
		Tr_expList expList = NULL;

		S_beginScope(venv);
		S_beginScope(tenv);

		while (decList)
		{
			Tr_add_exp(transDec(level, breakk, venv, tenv, decList->head), &expList);
			decList = decList->tail;
		}
		struct expty letBodyExpTy = transExp(level, breakk, venv, tenv, e->u.let.body);
		Tr_add_exp(letBodyExpTy.exp, &expList);

		S_endScope(venv);
		S_endScope(tenv);

		if (level->parent == NULL)
			Tr_procEntryExit(level, Tr_seqExp(expList), Tr_formals(level));

		return expTy(Tr_seqExp(expList), letBodyExpTy.ty);
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
static		 Tr_exp transDec(Tr_level level, Tr_exp breakk, S_table venv, S_table tenv, A_dec d){
	switch (d->kind) 
	{
	case A_functionDec:
	{
		A_fundecList fundecList = d->u.function;
		A_fieldList paramFieldList;
		Ty_tyList formalTyLists;
		Ty_ty resultTy;
		while (fundecList)
		{			
/*--------------------------------------Examine return type------------------------------------------*/
			if (!fundecList->head->result) 
				resultTy = Ty_Void();
			else
			{
				resultTy = S_look(tenv, fundecList->head->result);
				if (!resultTy)
				{
					EM_error(fundecList->head->pos, "Return type \'%s\' is undefined.", S_name(fundecList->head->result));
					resultTy = Ty_Void();
				}
			}
/*----------------------------Push function decelaration into venv----------------------------------*/
			Ty_ty paramTy;
			Ty_tyList formalTyList = NULL;
			formalTyLists = formalTyList;
			paramFieldList = fundecList->head->params;
			while (paramFieldList)
			{
				paramTy = S_look(tenv, paramFieldList->head->typ);
				if (!paramTy)
				{
					EM_error(paramFieldList->head->pos, "Parameter type \'%s\' is undefined!", S_name(paramFieldList->head->typ));
					paramTy = Ty_Int();
				}
				else if (!formalTyList) 
				{
					formalTyList = Ty_TyList(paramTy, NULL);
					formalTyLists = formalTyList;
				}
				else
				{
					formalTyList->tail = Ty_TyList(paramTy, NULL);
					formalTyList = formalTyList->tail;
				}
				paramFieldList = paramFieldList->tail;
			}

/*------------------------------------------Create new level---------------------------------------------*/
			Temp_label label = Temp_newlabel();
			U_boolList boolList_head = NULL;
			U_boolList boolList_tail = NULL;
			paramFieldList = fundecList->head->params;
			while (paramFieldList)
			{
				if (boolList_head)
				{
					boolList_tail->tail = U_BoolList(TRUE, NULL);
					boolList_tail = boolList_tail->tail;
				}
				else
				{
					boolList_head = U_BoolList(TRUE, NULL);
					boolList_tail = boolList_head;
				}
				paramFieldList = paramFieldList->tail;
			}
			Tr_level newLevel = Tr_newLevel(level, label, boolList_head);
			S_enter(venv, fundecList->head->name, E_FunEntry(newLevel, label, formalTyLists, resultTy));
						
			fundecList = fundecList->tail;
		}
/*--------------------------------------Function body part--------------------------------------------------*/
		Ty_tyList formalTy;
		fundecList = d->u.function;
		while (fundecList)
		{
			E_enventry funEntry = S_look(venv, fundecList->head->name);
			/*-----------------------------------S_beginScope---------------------------------------------*/
			S_beginScope(venv);

			formalTyLists = funEntry->u.fun.formals;
			formalTy = formalTyLists;
			paramFieldList = fundecList->head->params;
			Tr_accessList accessList = Tr_formals(funEntry->u.fun.level);
			struct expty bodyExpTy;
			while (accessList && paramFieldList && formalTy)
			{
				S_enter(venv, paramFieldList->head->name, E_VarEntry(accessList->head, formalTy->head));
				accessList = accessList->tail;
				paramFieldList = paramFieldList->tail;
				formalTy = formalTy->tail;
			}
			E_enventry funName = S_look(venv, fundecList->head->name);
			bodyExpTy = transExp(funEntry->u.fun.level, breakk, venv, tenv, fundecList->head->body);
			if (!equal_ty(funName->u.fun.result, bodyExpTy.ty))
				EM_error(fundecList->head->pos, "Return type of function \'%s\' is incorrect.", S_name(fundecList->head->name));
			Tr_procEntryExit(funEntry->u.fun.level, bodyExpTy.exp, accessList);
			S_endScope(venv);
			/*--------------------------------------S_endScope------------------------------------------*/
			fundecList = fundecList->tail;
		}
		return Tr_noExp();
	}
	case A_varDec:
	{
		struct expty initExpTy = transExp(level, breakk, venv, tenv, d->u.var.init);
		Tr_access access = Tr_allocLocal(level, d->u.var.escape);
		/*var with type decelaration, e.g.: var a:int := 0*/
		if (d->u.var.typ)
		{
			Ty_ty varTy = S_look(tenv, d->u.var.typ);
			if (!varTy)
				EM_error(d->pos, "Type \'%s\' is undefined.", S_name(d->u.var.typ));
			else if (!equal_ty(varTy, initExpTy.ty))
			{
				EM_error(d->pos, "Type \'%s\' doesn't match definition.", S_name(d->u.var.typ));
				S_enter(venv, d->u.var.var, E_VarEntry(access, varTy));
			}
			else
				S_enter(venv, d->u.var.var, E_VarEntry(access, varTy));			
		}
		/*var without type decelaration, e.g.: var a:= 0.*/
		else 
		{
			if (initExpTy.ty->kind == Ty_void || initExpTy.ty->kind == Ty_nil)
			{
				EM_error(d->pos, "Initial value type is invalid for \'%s\'", S_name(d->u.var.var));
				S_enter(venv, d->u.var.var, E_VarEntry(access, Ty_Int()));
			}
			else
				S_enter(venv, d->u.var.var, E_VarEntry(access, initExpTy.ty));
		}
		return Tr_assignExp(Tr_simpleVar(access, level), initExpTy.exp);
	}
	case A_typeDec:
	{
		Ty_ty nameTy;
		bool Cycle = TRUE;
		A_nametyList typeList = d->u.type;
		while (typeList)
		{
			S_enter(tenv, typeList->head->name, Ty_Name(typeList->head->name, NULL));
			typeList = typeList->tail;
		}			
		typeList = d->u.type;
		while (typeList)
		{
			Ty_ty typeTy = transTy(tenv, typeList->head->ty);
			if (Cycle && typeTy->kind != Ty_name)
				Cycle = FALSE;
			nameTy = S_look(tenv, typeList->head->name);
			nameTy->u.name.ty = typeTy;
			typeList = typeList->tail;
		}
		if (Cycle)
			EM_error(d->pos, "Illegal Cycle.");
		return Tr_noExp();
	}
	default:
		assert(0);
	}
}
static		  Ty_ty transTy	(								S_table tenv,				A_ty  t)
{
	switch (t->kind)
	{
	case A_nameTy:
	{
		Ty_ty nameTy = S_look(tenv, t->u.name);
		if (!nameTy) 
		{
			EM_error(t->pos, "Type \'%s\' is undefined.", S_name(t->u.name));
			return Ty_Int();
		}
		else 
			return nameTy;

	}
	case A_recordTy:
	{
		A_fieldList recordFieldList = t->u.record;
		Ty_fieldList TyList = NULL;
		Ty_fieldList tyHead = NULL;
		Ty_ty tyRecordHead;
		Ty_field tempTy;
		while (recordFieldList)
		{
			tyRecordHead = S_look(tenv, recordFieldList->head->typ);
			if (!tyRecordHead)
				EM_error(recordFieldList->head->pos, "Type \'%s\' is undefined.", S_name(recordFieldList->head->typ));
			else
			{
				tempTy = Ty_Field(recordFieldList->head->name, tyRecordHead);
				if (!TyList)
				{
					TyList = Ty_FieldList(tempTy, NULL);
					tyHead = TyList;
				}
				else
				{
					TyList->tail = Ty_FieldList(tempTy, NULL);
					TyList = TyList->tail;
				}
			}
			recordFieldList = recordFieldList->tail;
		}
		return Ty_Record(tyHead);
	}		
	case A_arrayTy:
	{
		Ty_ty arrayTy = S_look(tenv, t->u.array);
		if (!arrayTy)
			EM_error(t->pos, "Type \'%s\' is undefined.", S_name(t->u.array));
		return Ty_Array(arrayTy);
	}
	default:
		assert(0);
	}
}
