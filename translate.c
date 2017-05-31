#include "absyn.h"
#include "temp.h"
#include "tree.h"
#include "frame.h"
#include "translate.h"


struct Cx{patchList trues; patchList falses; T_stm stm;};

struct Tr_exp_
{
	enum{Tr_ex, Tr_nx, Tr_cx} kind;
	union{T_exp ex; T_stm nx; struct Cx cx;} u;
};

struct Tr_level_ { //need revise
	Tr_level parent;
	Temp_label name;
	F_frame frame;
	Tr_accessList formals;
};

struct Tr_access_ {
	Tr_level level;
	F_access access;
};

struct Tr_expList_ {
	Tr_exp head;
	Tr_expList tail;
};

struct patchList_ 
{
	Temp_label *head;
	patchList tail;
};

static Tr_exp Tr_Ex(T_exp ex);
static Tr_exp Tr_Nx(T_stm nx);
static Tr_exp Tr_Cx(patchList trues, patchList falses, T_stm stm);
static patchList PatchList(Temp_label *head, patchList tail);
static void doPatch(patchList pList, Temp_label label);
static patchList joinPatch(patchList fList, patchList sList);
static Tr_accessList extractFormalAccessList(Tr_level level);

static T_exp unEx(Tr_exp e);
static T_stm unNx(Tr_exp e);
static struct Cx unCx(Tr_exp e);
static Tr_level outerlevel = NULL;


/*omitted*/
Tr_accessList Tr_AccessList(Tr_access h, Tr_accessList t) {
	Tr_accessList al = checked_malloc(sizeof(*al));
	al->head = h;
	al->tail = t;
	return al;
}

static Tr_exp Tr_Ex(T_exp ex) //tree expression(with return value)
{
	Tr_exp tr_ex = checked_malloc(sizeof(*tr_ex));
	tr_ex->kind = Tr_ex;
	tr_ex->u.ex = ex;
	return tr_ex;
}
static Tr_exp Tr_Nx(T_stm nx) //tree non-expression(a statement)
{
	Tr_exp tr_nx = checked_malloc(sizeof(*tr_nx));
	tr_nx->kind = Tr_nx;
	tr_nx->u.nx = nx;
	return tr_nx;
}
static Tr_exp Tr_Cx(patchList trues, patchList falses, T_stm stm) // conditional expression
{
	Tr_exp tr_cx = checked_malloc(sizeof(*tr_cx));
	tr_cx->kind = Tr_cx;
	tr_cx->u.cx.trues = trues;
	tr_cx->u.cx.falses = falses;
	tr_cx->u.cx.stm = stm;
	return tr_cx;
}

static patchList PatchList(Temp_label *head, patchList tail) //labels need to be filled in
{
	patchList patch_list = checked_malloc(sizeof(*patch_list));
	patch_list->head = head;
	patch_list->tail = tail;
	return patch_list;
}


static void doPatch(patchList pList, Temp_label label)
{
	for (; pList; pList = pList->tail)
		*(pList->head) = label;
}

static patchList joinPatch(patchList fList, patchList sList)
{
	if (!fList) return sList;
	for (; fList->tail; fList = fList->tail)
		;
	fList->tail = sList;
	return fList;
}

static T_exp unEx(Tr_exp e) //convert other kind to Ex
{
	switch(e->kind) {
		case Tr_ex:
			return e->u.ex;
		case Tr_nx:
			return T_Eseq(e->u.nx, T_Const(0));
		case Tr_cx:
		{
			Temp_temp r = Temp_newtemp();
			Temp_label t = Temp_newlabel(), f = Temp_newlabel();
			doPatch(e->u.cx.trues, t);
			doPatch(e->u.cx.falses, f);
			return T_Eseq(T_Move(T_Temp(r), T_Const(1)),
				T_Eseq(e->u.cx.stm,
					T_Eseq(T_Label(f), 
						T_Eseq(T_Move(T_Temp(r), T_Const(0)),
							T_Eseq(T_Label(t), T_Temp(r))))));
		}
		default:
		{
			assert(0);
		}
	}
	return NULL;
}

static T_stm unNx(Tr_exp e) //convert other kind to Nx
{
	switch(e->kind) {
		case Tr_ex:
			return T_Exp(e->u.ex);
		case Tr_nx:
			return e->u.nx;
		case Tr_cx:
		{
			Temp_temp r = Temp_newtemp();
			Temp_label t = Temp_newlabel(), f = Temp_newlabel();
			doPatch(e->u.cx.trues, t);
			doPatch(e->u.cx.falses, f);
			return T_Exp(T_Eseq(T_Move(T_Temp(r), T_Const(1)),
				T_Eseq(e->u.cx.stm,
					T_Eseq(T_Label(f), 
						T_Eseq(T_Move(T_Temp(r), T_Const(0)),
							T_Eseq(T_Label(t), T_Temp(r)))))));
		}
		default:
		{
			assert(0);
		}
	}
	return NULL;
}

static struct Cx unCx(Tr_exp e) //convert other kind to Cx
{
	switch(e->kind) {
		case Tr_ex:
		{
			struct Cx cx;
			cx.stm = T_Cjump(T_eq, e->u.ex, T_Const(0), NULL, NULL);  
			cx.trues = PatchList(&(cx.stm->u.CJUMP.true), NULL);
			cx.falses = PatchList(&(cx.stm->u.CJUMP.false), NULL);
			return cx;
		}
		case Tr_nx:
			assert(0); // no such case
		case Tr_cx:
		{
			return e->u.cx;
		}
		default:
		{
			assert(0);
		}
	}
}

static Tr_access Tr_Access(Tr_level level, F_access access)
{
	Tr_access tr_access = checked_malloc(sizeof(*tr_access));
	tr_access->level = level;
	tr_access->access = access;
	return tr_access;
}

static Tr_accessList extractFormalAccessList(Tr_level level)
{
	Tr_accessList tr_head = NULL, tr_aList;
	F_accessList f_aList = F_formals(level->frame)->tail; // the first item is discarded because of static links
	
	while(f_aList) 
	{
		Tr_access tr_access = Tr_Access(level, f_aList->head);
		if (tr_head) 
		{
			tr_aList->tail = Tr_AccessList(tr_access, NULL);
			tr_aList = tr_aList->tail;
		} 
		else 
		{
			tr_head = Tr_AccessList(tr_access, NULL);
			tr_aList = tr_head;
		}
		f_aList = f_aList->tail;
	}
	return tr_head;
}

Tr_expList Tr_ExpList(Tr_exp head, Tr_expList tail) {
    Tr_expList tr_list = checked_malloc(sizeof(*tr_list));
	tr_list->head = head;
	tr_list->tail = tail;
	return tr_list;
}

void Tr_expList_annotate(Tr_exp head, Tr_expList * tr_explist) {
	Tr_expList tr_list = Tr_ExpList(head, NULL);
	tr_list->tail = *tr_explist;
	*tr_explist = tr_list;
}

Tr_level Tr_outermost(void)
{
	if (!outerlevel)
		outerlevel = Tr_newLevel(NULL, Temp_newlabel(), NULL);
	return outerlevel;
}

Tr_level Tr_newLevel(Tr_level parent, Temp_label name, U_boolList formals)
{
	Tr_level tr_level = checked_malloc(sizeof(*tr_level));
	tr_level->parent = parent;
	tr_level->name = name;
	tr_level->frame = F_newFrame(name, U_BoolList(TRUE, formals));
	tr_level->formals = extractFormalAccessList(tr_level);
	return tr_level;
}

Tr_accessList Tr_formals(Tr_level level)
{
	return level->formals;
}

Tr_access Tr_allocLocal(Tr_level level, bool escape)
{
	Tr_access tr_acc = checked_malloc(sizeof(*tr_acc));
	tr_acc->access = F_allocLocal(level->frame, escape);
	tr_acc->level = level;
	return tr_acc;
}

Tr_exp Tr_simpleVar(Tr_access access, Tr_level level)  //revised, level is the accessed level, access is the position of the variable
{
	T_exp fp = T_Temp(F_FP());
	Tr_level l;
	for(l = level;l != access->level; l = l->parent)
	{
		F_access static_link = F_formals(level->frame)->head;
		fp = F_Exp(static_link, fp);
	}
	return Tr_Ex(F_Exp(access->access, fp));
}

Tr_exp Tr_fieldVar(Tr_exp base, int offset) {
	T_exp addr = T_Binop(T_plus, unEx(base), T_Const(offset * F_WORD_SIZE));
	T_exp value = T_Mem(addr);
	return Tr_Ex(value);
}

Tr_exp Tr_subscriptVar(Tr_exp base, Tr_exp index) {
	T_exp addr = T_Binop(T_plus, unEx(base), T_Binop(T_mul, unEx(index), T_Const(F_WORD_SIZE)));
	T_exp value = T_Mem(addr);
	return Tr_Ex(value);
}

Tr_exp Tr_binOpExp(A_oper op, Tr_exp left_exp, Tr_exp right_exp)
{
	T_binOp t_binop;
	switch(op)
	{
		case A_plusOp: t_binop =  T_plus; break;
		case A_minusOp: t_binop = T_minus; break;
		case A_timesOp: t_binop =  T_mul; break;
		case A_divideOp: t_binop = T_div; break;
	}
	return Tr_Ex(T_Binop(t_binop, unEx(left_exp), unEx(right_exp)));
}

Tr_exp Tr_relOpExp(A_oper op, Tr_exp left_exp, Tr_exp right_exp) //default signed int
{
	T_relOp t_relop;
	switch(op) 
	{
		case A_eqOp: t_relop = T_eq; break;
		case A_neqOp: t_relop = T_ne; break;
		case A_ltOp: t_relop = T_lt; break;
		case A_leOp: t_relop = T_le; break;
		case A_gtOp: t_relop = T_gt; break;
		case A_geOp: t_relop = T_ge; break;
		default: assert(0); /* should never happen*/
	}
	T_stm stm = T_Cjump(t_relop, unEx(left_exp), unEx(right_exp), NULL, NULL);
	patchList trues = PatchList(&(stm->u.CJUMP.true), NULL);
	patchList falses = PatchList(&(stm->u.CJUMP.false), NULL);
	return Tr_Cx(trues, falses, stm);
}

Tr_exp Tr_intExp(int i)
{
	T_exp int_exp = T_Const(i);
	return Tr_Ex(int_exp);
}

Tr_exp Tr_noExp()
{
	T_exp no_exp = T_Const(0);
	return Tr_Ex(no_exp);
}

static Temp_temp nil_temp = NULL;
Tr_exp Tr_nilExp()
{
	if (!nil_temp) {
		nil_temp = Temp_newtemp(); 
		T_stm t_malloc = T_Move(T_Temp(nil_temp), F_externalCall(String("malloc"), T_ExpList(T_Const(0), NULL)));
		return Tr_Ex(T_Eseq(t_malloc, T_Temp(nil_temp)));
	}
	return Tr_Ex(T_Temp(nil_temp));
}

Tr_exp Tr_callExp(Temp_label fun_name, Tr_level fun_def, Tr_level fun_call, Tr_expList * arg_list) //function call
{

	T_exp fp = T_Temp(F_FP());
	while(fun_call && (fun_call != fun_def->parent))
	{
		F_access f_acc = F_formals(fun_call->frame)->head;
		fp = F_Exp(f_acc, fp);
		fun_call = fun_call->parent;
	}
	Tr_exp addr = Tr_Ex(fp);
	Tr_expList_annotate(addr, arg_list);

	T_expList args = NULL, list = NULL;
	while(*arg_list)
	{
		T_exp node = unEx((*arg_list)->head);
		if(args)
		{
			list->tail = T_ExpList(node, NULL);
			list = list->tail;
		}
		else
		{
			args = T_ExpList(node, NULL);
			list = args;
		}
		(*arg_list) = (*arg_list)->tail;
	}

	return Tr_Ex(T_Call(T_Name(fun_name), args));
}

Tr_exp Tr_recordExp(int size, Tr_expList initList)
{
	int i;
	Temp_temp r = Temp_newtemp();
	T_expList args = T_ExpList(T_Const(size * F_WORD_SIZE), NULL);
	T_stm t_malloc = T_Move(T_Temp(r), F_externalCall(String("malloc"), args));
	T_stm t_seq = T_Move(T_Mem(T_Binop(T_plus,T_Temp(r), T_Const((size-1)*F_WORD_SIZE))), unEx(initList->head));
	T_stm t_mv;
	for(i = size-1; i > 0; i++)
	{
		t_mv = T_Move(T_Mem(T_Binop(T_plus,T_Temp(r), T_Const((i-1)*F_WORD_SIZE))), unEx(initList->head));
		t_seq = T_Seq(t_mv, t_seq);
		initList = initList->tail; 
	}
	return Tr_Ex(T_Eseq(T_Seq(t_malloc, t_seq), T_Temp(r)));

}
Tr_exp Tr_arrayExp(Tr_exp size, Tr_exp init)
{
	T_expList args = T_ExpList(unEx(size), T_ExpList(unEx(init), NULL));
	T_exp func_call = F_externalCall(String("initArray"), args);
	return Tr_Ex(func_call);
}

Tr_exp Tr_ifExp(Tr_exp e1, Tr_exp e2, Tr_exp e3)
{
	Temp_label t = Temp_newlabel(), f = Temp_newlabel(), join = Temp_newlabel();
	struct Cx c1 = unCx(e1);
	doPatch(c1.trues, t);
	doPatch(c1.falses, f);
	if(e3)
	{
		T_stm e2_stm, e3_stm, join_stm;
		Temp_temp r = Temp_newtemp();
		join_stm = T_Jump(T_Name(join), Temp_LabelList(join, NULL));
		switch(e2->kind)
		{
			case Tr_ex: e2_stm = T_Exp(e2->u.ex); break; 
			case Tr_nx: e2_stm = e2->u.nx; break; 
			case Tr_cx: e2_stm = e2->u.cx.stm; break; 
		}
		switch(e3->kind)
		{
			case Tr_ex: e3_stm = T_Exp(e3->u.ex); break; 
			case Tr_nx: e3_stm = e3->u.nx; break; 
			case Tr_cx: e3_stm = e3->u.cx.stm; break; 
		}
		return Tr_Nx(T_Seq(c1.stm, T_Seq(T_Label(t), T_Seq(e2_stm, T_Seq(join_stm, T_Seq(T_Label(f), T_Seq(e3_stm, T_Seq(join_stm, T_Label(join))))))))); 
	}
	else
	{
		switch(e2->kind)
		{
			case Tr_ex:
			{
				return Tr_Nx(T_Seq(c1.stm, T_Seq(T_Label(t), T_Seq(T_Exp(unEx(e2)), T_Label(f))))); break;
			}
			case Tr_nx:
			{
				return Tr_Nx(T_Seq(c1.stm, T_Seq(T_Label(t), T_Seq(e2->u.nx, T_Label(f))))); break;
			}
			case Tr_cx:
			{
				return Tr_Nx(T_Seq(c1.stm, T_Seq(T_Label(t), T_Seq(e2->u.cx.stm, T_Label(f))))); break;
			}

		}

	}
}

Tr_exp Tr_doneExp()
{
	T_exp done_label = T_Name(Temp_newlabel());
	return Tr_Ex(done_label);
}
Tr_exp Tr_whileExp(Tr_exp test, Tr_exp body, Tr_exp done)
{
	Temp_label test_label = Temp_newlabel(), body_label = Temp_newlabel();
	return Tr_Ex(T_Eseq(T_Jump(T_Name(test_label), Temp_LabelList(test_label, NULL)), 
				        T_Eseq(T_Label(body_label),
							   T_Eseq(unNx(body),
								      T_Eseq(T_Label(test_label),
								             T_Eseq(T_Cjump(T_eq, unEx(test), T_Const(0), unEx(done)->u.NAME, body_label),
										            T_Eseq(T_Label(unEx(done)->u.NAME), T_Const(0))))))));
}
Tr_exp Tr_assignExp(Tr_exp left_value, Tr_exp value)
{
	T_stm assign_exp = T_Move(unEx(left_value), unEx(value));
	return Tr_Nx(assign_exp);
}
Tr_exp Tr_breakExp(Tr_exp done_label)
{
	T_stm jump_stm = T_Jump(T_Name(unEx(done_label)->u.NAME), Temp_LabelList(unEx(done_label)->u.NAME, NULL));
	return Tr_Nx(jump_stm);
}

Tr_exp Tr_seqExp(Tr_expList tr_explist)
{
	T_exp seq = unEx(tr_explist->head);
	tr_explist = tr_explist->tail;
	while(tr_explist)
	{
		seq = T_Eseq(T_Exp(unEx(tr_explist->head)), seq);
		tr_explist = tr_explist->tail;
	} 
	return Tr_Ex(seq);
}

Tr_exp Tr_eqStringExp(A_oper op, Tr_exp left_exp, Tr_exp right_exp)
{
	T_expList arg_list = T_ExpList(unEx(left_exp), T_ExpList(unEx(right_exp), NULL));
	T_exp res = F_externalCall(String("stringEqual"), arg_list);
	switch(op)
	{
		case A_eqOp:
		{
			return Tr_Ex(res);
		} 
		case A_neqOp:
		{
			return (res->kind == T_CONST && res->u.CONST == 1) ? Tr_Ex(T_Const(0)): Tr_Ex(T_Const(1));
		}
	}
}

static F_fragList stringFragList = NULL;  //string list
Tr_exp Tr_stringExp(string s) { 
	Temp_label label = Temp_newlabel();
	F_frag string_frag = F_StringFrag(label, s);
	stringFragList =  F_FragList(string_frag, stringFragList);
	return Tr_Ex(T_Name(label));
}

static F_fragList fragList = NULL;   //proc list
void Tr_procEntryExit(Tr_level level, Tr_exp body, Tr_accessList formals)
{
	F_frag proc_frag = F_ProcFrag(unNx(body), level->frame);
	fragList = F_FragList(proc_frag, fragList);
}



F_fragList Tr_getResult(void)  //need revise
{
	F_fragList cursor = NULL, prev = NULL;
	for (cursor = stringFragList; cursor; cursor = cursor->tail)
		prev = cursor;
	if (prev) prev->tail = fragList;
	return stringFragList ? stringFragList : fragList;
}