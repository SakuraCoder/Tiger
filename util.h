#include <assert.h>

typedef char *string;
typedef char bool;

#define TRUE 1
#define FALSE 0
#define MAX_LENGTH 65535

void *checked_malloc(int);
string String(char *);

typedef struct U_boolList_ *U_boolList;
struct U_boolList_ { bool head; U_boolList tail; };

U_boolList U_BoolList(bool head, U_boolList tail);
#define F_TEMPMAP (F_tempMap ? F_tempMap : (F_tempMap = Temp_empty()))
#define TL Temp_TempList