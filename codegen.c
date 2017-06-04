#include <stdio.h>
#include <string.h>
#include "symbol.h"
#include "temp.h"
#include "tree.h"
#include "frame.h"
#include "assem.h"
#include "printtree.h"

extern Temp_map F_tempMap;
static F_frame Co_frame = NULL; /* current function frame */

static void emit(AS_instr);
static Temp_temp munchExp(T_exp);
static void munchStm(T_stm);
static Temp_tempList munchArgs(int, T_expList);
inline void match_op(int I, char *op, char *sign)
{
    memset(op, 0, 100);
    memset(sign, 0, 100);
    switch(I)
    {
        case T_plus: strcpy(op, "add"); strcpy(sign, "+");break;
        case T_minus: strcpy(op, "sub"); strcpy(sign, "-");break;
        case T_mul: strcpy(op, "mul"); strcpy(sign, "*");break;
        case T_div: strcpy(op, "div"); strcpy(sign, "/");break;
        default: assert( 0 && "invalid Oper");
    }
}


inline void write_asmstringstr(char *asm_string, char* str, char* arg)
{
    sprintf(asm_string, str, arg);
}
inline void write_asmstringint(char *asm_string, char* str, int arg)
{
    sprintf(asm_string, str, arg);
}
inline void write_asmstringstrint(char *asm_string, char* str, char* arg1, int arg2)
{
    sprintf(asm_string, str, arg1, arg2);
}
inline void move(string p2asm_str, char *asm_string, T_exp dst, T_exp src, int constt)
{
    sprintf(asm_string, "mov `s1, %d(`s0)", constt); 
    p2asm_str = String(asm_string); 
    emit(AS_Move(p2asm_str, NULL, TL(munchExp(dst), TL(munchExp(src), NULL))));
}

inline void match_cmp(int I, char *op){
    memset(op,0,100);
    switch(I){
        case T_eq: strcpy(op, "je"); break; 
        case T_ne: strcpy(op, "jne"); break; 
        case T_lt: strcpy(op, "jl"); break; 
        case T_gt: strcpy(op, "jg"); break; 
        case T_le: strcpy(op, "jle"); break; 
        case T_ge: strcpy(op, "jge"); break; 
        default: assert(0 && "Invalid CMP SIGN"); 
    }
}

static Temp_temp munchExp(T_exp e)
{
    char assem_string[100];
    string p2asm_str;
    Temp_temp r = Temp_newtemp(); 

    switch (e->kind) 
    {
        case T_BINOP: 
        {
            char op[100], sign[100];
            T_exp left = e->u.BINOP.left;
            T_exp right = e->u.BINOP.right;
            match_op(e->u.BINOP.op, op, sign);
            
            if (left->kind == T_CONST)
            {
                write_asmstringstrint(assem_string, "%s $%x, `d0", op, left->u.CONST);   
                p2asm_str = String(assem_string);
                emit(AS_Oper(p2asm_str, TL(r = munchExp(right), NULL), NULL, NULL));
            } 
            else if (e->u.BINOP.right->kind == T_CONST) 
            {
                write_asmstringstrint(assem_string, "%s $%x, `d0", op, right->u.CONST);
                p2asm_str = String(assem_string);  
                emit(AS_Oper(p2asm_str, TL(r = munchExp(left), NULL), NULL, NULL));
            } 
            else 
            { 
                write_asmstringstr(assem_string, "%s `s0, `d0", op);
                p2asm_str = String(assem_string);
                emit(AS_Oper(p2asm_str, TL(r = munchExp(right), NULL), TL(munchExp(left), NULL), NULL));
            }
            return r;
        }
        case T_MEM: 
        {
            T_exp mem = e->u.MEM;
            if (mem->kind == T_BINOP && mem->u.BINOP.op == T_plus) 
            {
                T_exp left = mem->u.BINOP.left, right = mem->u.BINOP.right;
                if (left->kind == T_CONST) 
                { 
                    write_asmstringint(assem_string, "mov %d(`s0), `d0", left->u.CONST);
                    p2asm_str = String(assem_string);
                    emit(AS_Move(p2asm_str, TL(r, NULL), TL(munchExp(right), NULL)));
                } 
                else if (right->kind == T_CONST) 
                { 
                    write_asmstringint(assem_string, "mov %d(`s0), `d0", right->u.CONST);
                    p2asm_str = String(assem_string);
                    emit(AS_Move(p2asm_str, TL(r, NULL), TL(munchExp(left), NULL)));
                } 
                else
                { 
                	assert(0 && "invalid MEM-BINOP"); 
                }
            } 
            else if (mem->kind == T_CONST) 
            {
                write_asmstringint(assem_string, "mov ($0x%x), `d0", mem->u.CONST);
                p2asm_str = String(assem_string);
                emit(AS_Move(p2asm_str, TL(r, NULL), NULL));
            } 
            else 
            {
                emit(AS_Move(String("mov (`s0), `d0"), TL(r, NULL), TL(munchExp(mem->u.MEM), NULL)));
            }
            return r;
        }
        case T_TEMP: return e->u.TEMP;
        case T_ESEQ: 
        {
        	munchStm(e->u.ESEQ.stm); 
        	return munchExp(e->u.ESEQ.exp);
        }
        case T_NAME: 
        {
        	Temp_enter(F_TEMPMAP, r, Temp_labelstring(e->u.NAME)); 
        	return r;
        }
        case T_CONST: 
        {
            write_asmstringint(assem_string,"mov $0x%x, `d0", e->u.CONST);
            p2asm_str = String(assem_string);
            emit(AS_Move(p2asm_str, TL(r, NULL), NULL));
            return r;
        }
        case T_CALL: 
        {
            r = munchExp(e->u.CALL.fun);
            emit(AS_Oper(String("call `s0"), F_calldefs(), TL(r, munchArgs(0, e->u.CALL.args)), NULL));
            return r; 
        }
        default: 
        {
        	assert(0 && "invalid T_exp");
        }
    }
}

static void munchStm(T_stm s)
{
    char assem_string[100];
    string p2asm_str;

    switch (s->kind) 
    {
    	case T_SEQ: 
        {
        	munchStm(s->u.SEQ.left); 
        	munchStm(s->u.SEQ.right); 
        	break;
        }
        case T_LABEL: 
        {
            write_asmstringstr(assem_string,"%s", Temp_labelstring(s->u.LABEL));
            p2asm_str = String(assem_string);
            emit(AS_Label(p2asm_str, s->u.LABEL)); 
            break;
        }
        case T_JUMP: 
        {
            Temp_temp r = munchExp(s->u.JUMP.exp);
            emit(AS_Oper(String("jmp `d0"), TL(r, NULL), NULL, AS_Targets(s->u.JUMP.jumps)));
            break;
        }
        case T_MOVE:
        {
            T_exp dst = s->u.MOVE.dst, src = s->u.MOVE.src;
            if (dst->kind == T_MEM) 
            {
                if (dst->u.MEM->kind == T_BINOP && dst->u.MEM->u.BINOP.op == T_plus) 
                {
                    if (dst->u.MEM->u.BINOP.right->kind == T_CONST) 
                    {
                        move(p2asm_str, assem_string, dst->u.MEM->u.BINOP.left, src, dst->u.MEM->u.BINOP.right->u.CONST); 
                    } 
                    if (dst->u.MEM->u.BINOP.left->kind == T_CONST) 
                    { 
                        move(p2asm_str, assem_string, dst->u.MEM->u.BINOP.right, src, dst->u.MEM->u.BINOP.left->u.CONST);         
                    }
                } 
                else if (dst->u.MEM->kind == T_CONST) 
                { 
                    write_asmstringint(assem_string,"mov `s0, (%d)", dst->u.MEM->u.CONST);
                    p2asm_str = String(assem_string);
                    emit(AS_Move(p2asm_str, NULL, TL(munchExp(src), NULL)));
                } 
                else if (src->kind == T_MEM) 
                {
                    emit(AS_Move("mov `s1, (`s0)", NULL, TL(munchExp(dst->u.MEM), TL(munchExp(src->u.MEM), NULL))));
                } 
                else 
                { 
                    emit(AS_Move(String("mov `s1, (`s0)"), NULL, TL(munchExp(dst->u.MEM), TL(munchExp(src), NULL))));
                }   
            } 
            else if(dst->kind == T_TEMP) 
            { 
                emit(AS_Move(String("mov `s0, `d0"), TL(munchExp(dst), NULL), TL(munchExp(src), NULL)));    
            } 
            else
            { 
            	assert(0 && "MOVE dst error");
            }
            break;
        }

        case T_CJUMP: 
        {
            char cmp[100];
            Temp_temp left = munchExp(s->u.CJUMP.left), right = munchExp(s->u.CJUMP.right);
            emit(AS_Oper(String("cmp `s0, `s1"), NULL, TL(left, TL(right, NULL)), NULL));
            match_cmp(s->u.CJUMP.op, cmp);  
            write_asmstringstr(assem_string, "%s `j0", cmp);
            p2asm_str = String(assem_string);
            emit(AS_Oper(p2asm_str, NULL, NULL, AS_Targets(Temp_LabelList(s->u.CJUMP.true, NULL))));
            break;  
        }
        case T_EXP: munchExp(s->u.EXP); break;
        default: assert("Invalid T_stm" && 0);
    }
}

static Temp_tempList munchArgs(int i, T_expList args) 
{
    if (!args) 
    {
    	return NULL;
    }
    Temp_tempList tlist = munchArgs(i + 1, args->tail);
    Temp_temp rarg = munchExp(args->head);
    emit(AS_Oper(String("push `s0"), NULL, TL(rarg, NULL), NULL));  
    return (rarg, tlist);
}

static AS_instrList iList = NULL, last = NULL;
static void emit (AS_instr ins) 
{
    if (!iList) 
    {
        last = iList = AS_InstrList(ins, NULL);
    } 
    else 
    {
        last = last->tail = AS_InstrList(ins, NULL);
    }
}

AS_instrList codegen(F_frame f, T_stmList stmlist)
{
    AS_instrList list = NULL;
    T_stmList sl;
    Co_frame = f;
    for (sl = stmlist; sl; sl = sl->tail) 
    {
        munchStm(sl->head);
    }
    list = iList;
    iList = last = NULL;
    return list;
}
