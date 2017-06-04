#include <stdio.h>
#include <stdlib.h>
typedef struct F_frame_ * F_frame;
typedef struct F_access_ * F_access;

typedef struct F_accessList_ * F_accessList;
struct F_accessList_ {F_access head; F_accessList tail;};

typedef struct F_frag_ *F_frag;
struct F_frag_ {
	enum {F_stringFrag, F_procFrag} kind;
	union {
		struct {
			Temp_label label;
			string str;
		} stringg;
		struct {
			T_stm body;
			F_frame frame;
		} proc;
	} u;
};

typedef struct F_fragList_ *F_fragList;
struct F_fragList_ {
	F_frag head;
	F_fragList tail;
};

F_frag F_StringFrag(Temp_label label, string str);
F_frag F_ProcFrag(T_stm body, F_frame frame);
F_fragList F_FragList(F_frag head, F_fragList tail);

F_frame F_newFrame(Temp_label name, U_boolList formals); 
Temp_label F_name(F_frame f);
F_accessList F_formals(F_frame f);
F_access F_allocLocal(F_frame f, bool escape);

Temp_temp F_FP(void);
Temp_temp F_RV();
Temp_tempList F_calldefs();

extern const int F_WORD_SIZE;
T_exp F_Exp(F_access acc, T_exp framePtr);
T_exp F_externalCall(string str, T_expList args);
T_stm F_procEntryExit1(F_frame frame, T_stm stm);
