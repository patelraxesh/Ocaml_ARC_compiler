#include <stdio.h>
#include <stdlib.h>

extern int our_code_starts_here(int* HEAP) asm("our_code_starts_here");
extern void error() asm("error");
extern int print(int val) asm("print");
extern int equal(int val1, int val2) asm("equal");
extern int* allocate(int amount_needed) asm("allocate");
extern void dereference_pointer(int* pointer) asm("dereference_pointer");
extern int decrement_pointer(int pointer) asm("decrement_pointer");
extern int increment_pointer(int pointer) asm("increment_pointer");
extern int* HEAP_END asm("HEAP_END");
extern int* STACK_BOTTOM asm("STACK_BOTTOM");

const int NUM_TAG_MASK   = 0x00000001;
const int TUPLE_TAG_MASK = 0x00000007;
const int BOOL_TRUE      = 0xFFFFFFFF;
const int BOOL_FALSE     = 0x7FFFFFFF;

const int ERR_COMP_NOT_NUM   = 1;
const int ERR_ARITH_NOT_NUM  = 2;
const int ERR_LOGIC_NOT_BOOL = 3;
const int ERR_IF_NOT_BOOL    = 4;
const int ERR_OVERFLOW       = 5;
const int ERR_GET_NOT_TUPLE  = 6;
const int ERR_GET_LOW_INDEX  = 7;
const int ERR_GET_HIGH_INDEX = 8;
const int ERR_INDEX_NOT_NUM  = 9;
const int ERR_OUT_OF_MEMORY  = 10;

size_t HEAP_SIZE;
int* STACK_BOTTOM;
int* HEAP;
int* HEAP_END;
int debug = 0;

int equal(int val1, int val2) {
  if(val1 == val2) { return BOOL_TRUE; }
  else { return BOOL_FALSE; }
}

int tupleCounter = 0;
void printHelp(FILE *out, int val) {
  if((val & NUM_TAG_MASK) == 0) {
    fprintf(out, "%d", val >> 1);
  }
  else if(val == BOOL_TRUE) {
    fprintf(out, "true");
  }
  else if(val == BOOL_FALSE) {
    fprintf(out, "false");
  }
  else if ((val & TUPLE_TAG_MASK) == 5) {
    fprintf(out, "<function>");
  }
  else if ((val & TUPLE_TAG_MASK) != 0) {
    int* addr = (int*)(val - 1);
    // Check whether we've visited this tuple already
    if ((*addr & 0x80000000) != 0) {
      fprintf(out, "<cyclic tuple %d>", (int)(*addr & 0x7FFFFFFF));
      return;
    }
    // Mark this tuple: save its length locally, then mark it
    int len = addr[0];
    *(addr) = 0x80000000 | (++tupleCounter);
    fprintf(out, "(");
    for (int i = 2; i <= len+1; i++) {
      if (i > 2) fprintf(out, ", ");
      printHelp(out, addr[i]);
    }
    fprintf(out, ")");
    // Unmark this tuple: restore its length
    *(addr) = len;
  }
  else {
    fprintf(out, "Unknown value: %#010x", val);
  }
}

int print(int val) {
  printHelp(stdout, val);
  printf("\n");
  return val;
}

void error(int i) {
  switch (i) {
  case ERR_COMP_NOT_NUM:
    fprintf(stderr, "comparison expected a number\n");
    break;
  case ERR_ARITH_NOT_NUM:
    fprintf(stderr, "arithmetic expected a number\n");
    break;
  case ERR_LOGIC_NOT_BOOL:
    fprintf(stderr, "logic expected a boolean\n");
    break;
  case ERR_IF_NOT_BOOL:
    fprintf(stderr, "if expected a boolean\n");
    break;
  case ERR_OVERFLOW:
    fprintf(stderr, "Integer overflow\n");
    break;
  case ERR_GET_NOT_TUPLE:
    fprintf(stderr, "get expected tuple\n");
    break;
  case ERR_GET_LOW_INDEX:
    fprintf(stderr, "index too small to get\n");
    break;
  case ERR_GET_HIGH_INDEX:
    fprintf(stderr, "index too large to get\n");
    break;
  case ERR_INDEX_NOT_NUM:
    fprintf(stderr, "get expected number for index\n");
    break;
  case ERR_OUT_OF_MEMORY:
    // because of arg, we deal with message at call loc; just exit.
    break;
  default:
    fprintf(stderr, "Unknown error code: %d\n", i);
  }
  exit(i);
}

int* allocate_pointer(int size){
    int size_n = size/4;
    int* node_start = (int*)calloc(size_n, sizeof(int));
    return node_start;
}


void dereference_pointer(int* pointer) {
  free(pointer);
  *pointer = 0x00000000;
}

int decrement_pointer(int pointer) {
  int pointer_val = pointer;
  if ((pointer_val & TUPLE_TAG_MASK) == 5){
    // Its a Lambda Function
    if (debug){printf("%x : Decrement called on lambda\n", pointer_val);}
    int* fun_p = pointer_val - 5;
    int arity = *(fun_p);
    int ref_count = *(fun_p+1);
    ref_count -= 1;
    *(fun_p+1) -= 1;
    if (ref_count <= 0){
      if (debug){printf("%x : Function deallocating\n", fun_p);}
      for (size_t i = 3; i < arity+3; i++) {
        int tagged_ptr = *(fun_p+i);
        if (((tagged_ptr & TUPLE_TAG_MASK) == 5) && (tagged_ptr > 0x100dd0)){
          // Decrement that function
          decrement_pointer(tagged_ptr);
          if (debug){printf("Function decremented\n");}
        }
        else if (((tagged_ptr & TUPLE_TAG_MASK) == 1) && (tagged_ptr > 0x100dd0)){
          // Decrement that Tuple
          decrement_pointer(tagged_ptr);
          if (debug){printf("Tuple decremented\n");}
        }
        else{
          // Do Nothing
        }
      }
      dereference_pointer(fun_p);
    }
  }
  else if ((pointer_val & TUPLE_TAG_MASK) == 1){
    if (debug){printf("%x : Decrement called on Tuple\n", pointer_val);}
    // Its a Tuple
    int* tuple_p = pointer_val - 1;
    int len = *(tuple_p);
    int ref_count = *(tuple_p+1);
    ref_count -= 1;
    *(tuple_p+1) -= 1;
    if (ref_count <= 0){
      if (debug){printf("%x : Tuple deallocating \n", tuple_p);}
      for (size_t i = 2; i < len+2; i++) {
        int tagged_ptr = *(tuple_p+i);
        if (((tagged_ptr & TUPLE_TAG_MASK) == 5) && (tagged_ptr > 0x100dd0)){
          // Decrement that function
          decrement_pointer(tagged_ptr);
          if (debug){printf("Function decremented\n");}
        }
        else if (((tagged_ptr & TUPLE_TAG_MASK) == 1) && (tagged_ptr > 0x100dd0)){
          // Decrement that Tuple
          decrement_pointer(tagged_ptr);
          if (debug){printf("Tuple decremented\n");}
        }
        else{
          // Do Nothing
        }
      }
      dereference_pointer(tuple_p);
    }
  }
  else{
    //Do nothing
  }
  return 0;
}

int increment_pointer(int pointer){
  int pointer_val = pointer;
  if ((pointer_val & TUPLE_TAG_MASK) == 5){
    // Its a Lambda Function
    int* fun_p = pointer_val - 5;
    int arity = *(fun_p);
    *(fun_p+1) += 1;
    if (debug){ printf("%x Function incremented main\n", fun_p); }
  }
  else if ((pointer_val & TUPLE_TAG_MASK) == 1){
    // Its a Tuple
    int* tuple_p = pointer_val - 1;
    int len = *(tuple_p);
    *(tuple_p+1) += 1;
    if (debug){ printf("%x Tuple incremented main\n", tuple_p); }
  }
  else{
    //Do nothing
  }
  return pointer;
}

int* allocate(int bytes_needed) {
  int* new = allocate_pointer(bytes_needed);
  if(debug){
    printf("\nSize: %d bytes\n", bytes_needed);
    printf("p    = %p\n", (void *) new);
    printf("value at p         = %d\n", *(new));
    printf("value before p + 1 = %d\n", *(new+1));
    printf("value after p + 1  = %d\n", *(new+1));
    printf("value at p + 2     = %d\n", *(new+2));
  }
  return new;
}

int main(int argc, char** argv) {
  if(argc > 1) {
    HEAP_SIZE = atoi(argv[1]);
  }
  else {
    HEAP_SIZE = 100000;
  }
  HEAP = (int*)calloc(HEAP_SIZE, sizeof (int));
  HEAP_END = HEAP + HEAP_SIZE;

  int result = our_code_starts_here(HEAP);

  print(result);
  return 0;
}
