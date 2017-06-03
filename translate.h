
typedef struct Tr_exp_ *Tr_exp;
typedef struct patchList_ *patchList;

typedef struct Tr_level_ *Tr_level;
typedef struct Tr_access_ *Tr_access;
typedef struct Tr_accessList_ *Tr_accessList;
typedef struct Tr_expList_ * Tr_expList;

struct Tr_accessList_ {
	Tr_access head;
	Tr_accessList tail;
};

struct Tr_access_ {
	Tr_level level;
	F_access access;
};

struct Tr_level_ {
	Tr_level parent;
	Temp_label name;
	F_frame frame;
	Tr_accessList formals;
};


void Tr_expList_prepend(Tr_exp head, Tr_expList * tr_explist);
Tr_level Tr_outermost(void);
Tr_level Tr_newLevel(Tr_level parent, Temp_label name, U_boolList formals);
Tr_accessList Tr_formals(Tr_level level);
Tr_access Tr_allocLocal(Tr_level level, bool escape);
Tr_accessList Tr_AccessList(Tr_access head, Tr_accessList tail);



Tr_exp Tr_simpleVar(Tr_access access, Tr_level level);  //simple variable definition
Tr_exp Tr_fieldVar(Tr_exp base, int offset);   //field selection 
Tr_exp Tr_subscriptVar(Tr_exp base, Tr_exp index); //array subscript

Tr_exp Tr_arithExp(A_oper, Tr_exp, Tr_exp);
Tr_exp Tr_relExp(A_oper, Tr_exp, Tr_exp);
Tr_exp Tr_intExp(int i); //int type
Tr_exp Tr_stringExp(string str); //string type
Tr_exp Tr_doubleExp(float);

Tr_exp Tr_noExp(); //no value
Tr_exp Tr_nilExp(); //nil value
Tr_exp Tr_callExp(Temp_label fun_name, Tr_level fun_def, Tr_level fun_call, Tr_expList * arg_list); //function call
Tr_exp Tr_recordExp(int size, Tr_expList initList);  //record creation
Tr_exp Tr_arrayExp(Tr_exp size, Tr_exp init); //array creation
Tr_exp Tr_ifExp(Tr_exp e1, Tr_exp e2, Tr_exp e3);

Tr_exp Tr_doneExp();
Tr_exp Tr_whileExp(Tr_exp test, Tr_exp body, Tr_exp done);
Tr_exp Tr_assignExp(Tr_exp left_value, Tr_exp value);
Tr_exp Tr_breakExp(Tr_exp done_label);
Tr_exp Tr_seqExp(Tr_expList tr_explist);
Tr_exp Tr_eseqExp(Tr_exp e1, Tr_exp e2);
Tr_exp Tr_eqStringExp(A_oper op, Tr_exp left_exp, Tr_exp right_exp);

Tr_exp Tr_eqExp(A_oper, Tr_exp, Tr_exp);
Tr_exp Tr_eqRef(A_oper, Tr_exp, Tr_exp);

void Tr_procEntryExit(Tr_level level, Tr_exp body, Tr_accessList formals);
F_fragList Tr_getResult();

void print_frag(F_fragList, FILE *);
