#include"temp.h"
#include "frame.h"
#include "util.h"
#include "tree.h"

const int F_WORD_SIZE = 4;
struct F_access_ {
	enum { inFrame, inReg } kind;
	union {
		int offset; /* inFrame */
		Temp_temp reg; /* inReg */
	} u;
};

struct F_frame_ {
	F_accessList formals; //location of all the formals
	int local_cnt;   //the number of formals allocated so far
	Temp_label name;  //the name of the frame
};

static F_access InFrame(int offset); // location in the frame
static F_access InReg(Temp_temp reg); //location in the register


static F_access InFrame(int offset)
{
	F_access f_acc = checked_malloc(sizeof(*f_acc));
	f_acc->kind = inFrame;
	f_acc->u.offset = offset;
	return f_acc;
}

static F_access InReg(Temp_temp reg)
{
	F_access f_acc = checked_malloc(sizeof(*f_acc));
	f_acc->kind = inReg;
	f_acc->u.reg = reg;
	return f_acc;
}

static F_accessList F_AccessList(F_access head, F_accessList tail)
{
	F_accessList list = checked_malloc(sizeof(*list));
	list->head = head;
	list->tail = tail;
	return list;
}

static F_accessList extractFormalAccessList(F_frame f, U_boolList formals)
{
	U_boolList formal;
	F_accessList f_list = checked_malloc(sizeof(*f_list));
	F_accessList f_head = NULL;
	int InFrame_cnt = 0;
	for (formal = formals; formal; formal = formal->tail) 
	{
		F_access f_acc = NULL;
		if (!formal->head)  //if not escape
		{
			f_acc = InReg(Temp_newtemp());
		} 
		else   // if escape
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
	}
	return f_head;
}

F_frame F_newFrame(Temp_label name, U_boolList formals)
{
	F_frame f = checked_malloc(sizeof(*f));
	f->name = name;
	f->formals = extractFormalAccessList(f, formals);
	f->local_cnt = 0;
	return f;
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
	f->local_cnt++;
	if (escape) 
		return InFrame(F_WORD_SIZE * (- (1+f->local_cnt))); // 1 reserved space for return address
	else
		return InReg(Temp_newtemp());
}

T_exp F_Exp(F_access acc, T_exp framePtr)  //return tree expression an access
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

T_exp F_externalCall(string str, T_expList args) //call external functions
{
	return T_Call(T_Name(Temp_namedlabel(str)), args);
}

static Temp_temp fp = NULL;
Temp_temp F_FP(void)  //return the position of fp
{
	if (!fp) 
	{
		fp = Temp_newtemp();  //remove second input 
		//F_add_to_map("ebp", fp);
	}
	return fp;
}

static Temp_temp rv = NULL;
Temp_temp F_RV(void)
{
	if (!rv) {
		rv = Temp_newtemp(); //remove second input
		//F_add_to_map("eax", rv);
	}
	return rv;
}

F_frag F_StringFrag(Temp_label label, string str)  //string fragment
{
	F_frag string_frag = checked_malloc(sizeof(*string_frag));
	string_frag->kind = F_stringFrag;
	string_frag->u.stringg.label = label;
	string_frag->u.stringg.str = str;
	return string_frag;
}

F_frag F_ProcFrag(T_stm body, F_frame frame) //proc fragment
{
	F_frag proc_frag = checked_malloc(sizeof(*proc_frag));
	proc_frag->kind = F_procFrag;
	proc_frag->u.proc.body = body;
	proc_frag->u.proc.frame = frame;
	return proc_frag;
}

F_fragList F_FragList(F_frag head, F_fragList tail)
{
	F_fragList frag_list = checked_malloc(sizeof(*frag_list));
	frag_list->head = head;
	frag_list->tail = tail;
	return frag_list;
}

T_stm F_procEntryExit1(F_frame frame, T_stm stm)
{
	return stm;
}