/*Author: Zihan Zhao*/
#include "absyn.h"
#include "types.h"
#include "temp.h"
#include "tree.h"
#include "frame.h"
#include "translate.h"
#include "env.h"
#include <stdlib.h>


/*Ty_ty environment*/
S_table E_base_tenv(void)
{
	S_table Ty_ty_BaseTable = S_empty();
	S_enter(Ty_ty_BaseTable, S_Symbol("int"), Ty_Int());
	S_enter(Ty_ty_BaseTable, S_Symbol("string"), Ty_String());

	return Ty_ty_BaseTable;
}

/*E_enventry environment*/
S_table E_base_venv(void) 
{
  S_table E_enventry_BaseTable = S_empty();

  /*Add basic functions of Tiger*/
  S_enter(E_enventry_BaseTable, S_Symbol("print"),		E_FunEntry(Tr_outermost(), Temp_newlabel(), Ty_TyList(Ty_String(), NULL), Ty_Void()));
  S_enter(E_enventry_BaseTable, S_Symbol("flush"),		E_FunEntry(Tr_outermost(), Temp_newlabel(), NULL, Ty_Void()));
  S_enter(E_enventry_BaseTable, S_Symbol("getchar"),	E_FunEntry(Tr_outermost(), Temp_newlabel(), NULL, Ty_String()));
  S_enter(E_enventry_BaseTable, S_Symbol("ord"),		E_FunEntry(Tr_outermost(), Temp_newlabel(), Ty_TyList(Ty_String(), NULL), Ty_Int()));
  S_enter(E_enventry_BaseTable, S_Symbol("chr"),		E_FunEntry(Tr_outermost(), Temp_newlabel(), Ty_TyList(Ty_Int(), NULL), Ty_String()));
  S_enter(E_enventry_BaseTable, S_Symbol("size"),		E_FunEntry(Tr_outermost(), Temp_newlabel(), Ty_TyList(Ty_String(), NULL), Ty_Int()));
  S_enter(E_enventry_BaseTable, S_Symbol("substring"),	E_FunEntry(Tr_outermost(), Temp_newlabel(), Ty_TyList(Ty_String(), Ty_TyList(Ty_Int(), Ty_TyList(Ty_Int(), NULL))), Ty_String()));
  S_enter(E_enventry_BaseTable, S_Symbol("concat"),		E_FunEntry(Tr_outermost(), Temp_newlabel(), Ty_TyList(Ty_String(), Ty_TyList(Ty_String(), NULL)), Ty_String()));
  S_enter(E_enventry_BaseTable, S_Symbol("not"),		E_FunEntry(Tr_outermost(), Temp_newlabel(), Ty_TyList(Ty_Int(), NULL), Ty_Int()));
  S_enter(E_enventry_BaseTable, S_Symbol("exit"),		E_FunEntry(Tr_outermost(), Temp_newlabel(), Ty_TyList(Ty_Int(), NULL), Ty_Void()));
  return E_enventry_BaseTable;
}

E_enventry E_VarEntry(Tr_access access, Ty_ty ty)
{
	E_enventry env = checked_malloc(sizeof(*env));

	env->kind = E_varEntry;
	env->u.var.access = access;
	env->u.var.ty = ty;
	return env;
}

E_enventry E_FunEntry(Tr_level level, Temp_label label, Ty_tyList formals, Ty_ty result)
{
	E_enventry env = checked_malloc(sizeof(*env));

	env->kind = E_funEntry;
	env->u.fun.formals = formals;
	env->u.fun.level = level;
	env->u.fun.label = label;
	env->u.fun.result  = result;

	return env;
}
