#include "symbol.h"
#include "temp.h"
#include "tree.h"
#include "frame.h"


const int F_WORD_SIZE = 4;  

struct F_access_ {
	enum {inFrame, inReg} kind;
	union {
		int offset;
		Temp_temp reg; 
	} u;
};

struct F_frame_ 
{
	int local_count;
	F_accessList formals;
	Temp_label name;
};

static F_access InFrame(int offset);
static F_access InReg(Temp_temp reg);

static F_access InFrame(int offset) {
	F_access f_acc = checked_malloc(sizeof(*f_acc));
	f_acc->kind = inFrame;
	f_acc->u.offset = offset;
	return f_acc;
}

static F_access InReg(Temp_temp in_r) {
	F_access f_acc = checked_malloc(sizeof(*f_acc));
	f_acc->kind = inReg;
	f_acc->u.reg = in_r;
	return f_acc;
}

static F_accessList makeFormalAccessList(F_frame, U_boolList);
static F_accessList F_AccessList(F_access head, F_accessList tail);


static F_accessList makeFormalAccessList(F_frame f, U_boolList formals) 
{
	U_boolList formal = formals;
	F_accessList f_list = checked_malloc(sizeof(*f_list));
	F_accessList f_head = NULL;
	F_access f_acc = NULL;
	int InFrame_cnt = 0;
	while(formal)
	{
		if (!formal->head) 
		{
			f_acc = InReg(Temp_newtemp());
		} 
		else 
		{
			f_acc = InFrame((1 + InFrame_cnt) * F_WORD_SIZE); //extra one space for control link
			InFrame_cnt++;
		}

		if (f_head) 
		{
			f_list->tail = F_AccessList(f_acc, NULL);
			f_list = f_list->tail;
		} 
		else 
		{
			f_head = F_AccessList(f_acc, NULL);
			f_list = f_head;
		}
		formal = formal->tail;
	}
	return f_head;
}

static F_accessList F_AccessList(F_access head, F_accessList tail) {
	F_accessList f_link = checked_malloc(sizeof(*f_link));
	f_link->head = head;
	f_link->tail = tail;
	return f_link;
}

F_frame F_newFrame(Temp_label name, U_boolList formals) {
	F_frame frame = checked_malloc(sizeof(*frame));
	frame->name = name;
	frame->formals = makeFormalAccessList(frame, formals);
	frame->local_count = 0;
	return frame;
}

Temp_label F_name(F_frame f)
{
	return f->name;
}


F_accessList F_formals(F_frame f) 
{
	return f->formals;
}

F_access F_allocLocal(F_frame f, bool escape) 
{
	int new_count = f->local_count + 1;
	f->local_count = new_count;
	if (escape) 
	{
		return InFrame(F_WORD_SIZE * (- (1+f->local_count))); // one extra space for return
	}
	else
	{
		return InReg(Temp_newtemp());
	}
	
}

T_exp F_Exp(F_access acc, T_exp framePtr)
{
	if (acc->kind == inFrame) 
	{
		return T_Mem(T_Binop(T_plus, framePtr, T_Const(acc->u.offset)));
	} 
	else 
	{
		return T_Temp(acc->u.reg);
	}
}


T_exp F_externalCall(string str, T_expList args) 
{
	T_exp fun_name = T_Name(Temp_namedlabel(str));
	return T_Call(fun_name, args);
}

static Temp_temp f_ptr = NULL;
Temp_temp F_FP(void) 
{ 
	if (!f_ptr) 
	{
		f_ptr  = Temp_newtemp();
	}
	return f_ptr;
}

static Temp_temp rv_ptr = NULL;
Temp_temp F_RV(void)
{
	if (!rv_ptr) 
	{
		rv_ptr = Temp_newtemp();
	}
	return rv_ptr;
}

F_frag F_StringFrag(Temp_label label, string str) {
	F_frag string_frag  = checked_malloc(sizeof(*string_frag));
	string_frag->kind = F_stringFrag;
	string_frag->u.stringg.label = label;
	string_frag->u.stringg.str = str;
	return string_frag;
}

F_frag F_ProcFrag(T_stm body, F_frame frame) {
	F_frag proc_frag = checked_malloc(sizeof(*proc_frag));
	proc_frag->kind = F_procFrag;
	proc_frag->u.proc.body = body;
	proc_frag->u.proc.frame = frame;
	return proc_frag;
}

F_fragList F_FragList(F_frag head, F_fragList tail) {
	F_fragList frag_list = checked_malloc(sizeof(*frag_list));
	frag_list->head = head;
	frag_list->tail = tail;
	return frag_list;
}

T_stm F_procEntryExit1(F_frame frame, T_stm stm) 
{
	return stm;
}
