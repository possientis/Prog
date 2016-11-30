#include "link.h"
#include "dict.h"
#include <stdio.h>

int dictionary_test(){
  Dictionary* a;
  Dictionary* b;
  int errCode = 0;
  fprintf(stderr, "Dictionary: starting unit test\n");
  // basic new  copy delete test
  a = Dictionary_new(); 
  b = Dictionary_copy(a);
  Dictionary_delete(a); 
  Dictionary_delete(b); 
  if(Dictionary_hasMemoryLeak()){
    fprintf(stderr,"Dictionary: unit test 1.0 failing\n");
    errCode = -1;
  }
  // isEmpty
  a = Dictionary_new();
  b = Dictionary_new();
  if(!Dictionary_isEmpty(a)){
    fprintf(stderr, "Dictionary: unit test 2.0 failing\n");
    errCode = -1;
  }
  if(!Dictionary_isEmpty(b)){
    fprintf(stderr, "Dictionary: unit test 2.1 failing\n");
    errCode = -1;
  }
  // first insert
  int val1 = 10;
  const char* str1 = "abc";
  
  Dictionary_insert(a, 1, &val1);
  Dictionary_insert(b, 10, str1);
  // dictionaries should not be empty
  if(Dictionary_isEmpty(a)){
    fprintf(stderr, "Dictionary: unit test 3.0 failing\n");
    errCode = -1;
  }
  if(Dictionary_isEmpty(b)){
    fprintf(stderr, "Dictionary: unit test 3.1 failing\n");
    errCode = -1;
  }
  // should fail
  const void* result;
  if(Dictionary_find(a, 0, &result)){
    fprintf(stderr, "Dictionary: unit test 3.2 failing\n");
    errCode = -1;
  }
  if(Dictionary_find(b, 0, &result)){
    fprintf(stderr, "Dictionary: unit test 3.3 failing\n");
    errCode = -1;
  }
  // should succeed
  if(!Dictionary_find(a, 1, &result)){
    fprintf(stderr, "Dictionary: unit test 3.4 failing\n");
    errCode = -1;
  } else{
    if(result != &val1){
      fprintf(stderr, "Dictionary: unit test 3.5 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 10, &result)){
    fprintf(stderr, "Dictionary: unit test 3.6 failing\n");
    errCode = -1;
  } else{
    if(result != str1){
      fprintf(stderr, "Dictionary: unit test 3.7 failing\n");
      errCode = -1;
    }
  }
  // second insert
  int val2 = 20;
  const char* str2 = "def";
  
  Dictionary_insert(a, 2, &val2);
  Dictionary_insert(b, 20, str2);
 // should fail
  if(Dictionary_find(a, 0, &result)){
    fprintf(stderr, "Dictionary: unit test 4.2 failing\n");
    errCode = -1;
  }
  if(Dictionary_find(b, 0, &result)){
    fprintf(stderr, "Dictionary: unit test 4.3 failing\n");
    errCode = -1;
  }
  // should succeed
  if(!Dictionary_find(a, 1, &result)){
    fprintf(stderr, "Dictionary: unit test 4.4 failing\n");
    errCode = -1;
  } else{
    if(result != &val1){
      fprintf(stderr, "Dictionary: unit test 4.5 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 10, &result)){
    fprintf(stderr, "Dictionary: unit test 4.6 failing\n");
    errCode = -1;
  } else{
    if(result != str1){
      fprintf(stderr, "Dictionary: unit test 4.7 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 2, &result)){
    fprintf(stderr, "Dictionary: unit test 4.8 failing\n");
    errCode = -1;
  } else{
    if(result != &val2){
      fprintf(stderr, "Dictionary: unit test 4.9 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 20, &result)){
    fprintf(stderr, "Dictionary: unit test 4.10 failing\n");
    errCode = -1;
  } else{
    if(result != str2){
      fprintf(stderr, "Dictionary: unit test 4.11 failing\n");
      errCode = -1;
    }
  }
  // third insert
  int val3 = 30;
  const char* str3 = "ghi";
  
  Dictionary_insert(a, 3, &val3);
  Dictionary_insert(b, 30, str3);
 // should fail
  if(Dictionary_find(a, 0, &result)){
    fprintf(stderr, "Dictionary: unit test 5.2 failing\n");
    errCode = -1;
  }
  if(Dictionary_find(b, 0, &result)){
    fprintf(stderr, "Dictionary: unit test 5.3 failing\n");
    errCode = -1;
  }
  // should succeed
  if(!Dictionary_find(a, 1, &result)){
    fprintf(stderr, "Dictionary: unit test 5.4 failing\n");
    errCode = -1;
  } else{
    if(result != &val1){
      fprintf(stderr, "Dictionary: unit test 5.5 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 10, &result)){
    fprintf(stderr, "Dictionary: unit test 5.6 failing\n");
    errCode = -1;
  } else{
    if(result != str1){
      fprintf(stderr, "Dictionary: unit test 5.7 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 2, &result)){
    fprintf(stderr, "Dictionary: unit test 5.8 failing\n");
    errCode = -1;
  } else{
    if(result != &val2){
      fprintf(stderr, "Dictionary: unit test 5.9 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 20, &result)){
    fprintf(stderr, "Dictionary: unit test 5.10 failing\n");
    errCode = -1;
  } else{
    if(result != str2){
      fprintf(stderr, "Dictionary: unit test 5.11 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 3, &result)){
    fprintf(stderr, "Dictionary: unit test 5.12 failing\n");
    errCode = -1;
  } else{
    if(result != &val3){
      fprintf(stderr, "Dictionary: unit test 5.13 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 30, &result)){
    fprintf(stderr, "Dictionary: unit test 5.14 failing\n");
    errCode = -1;
  } else{
    if(result != str3){
      fprintf(stderr, "Dictionary: unit test 5.15 failing\n");
      errCode = -1;
    }
  }

  // fourth insert
  int val4 = 40;
  const char* str4 = "jkl";
  
  Dictionary_insert(a, 4, &val4);
  Dictionary_insert(b, 40, str4);
 // should fail
  if(Dictionary_find(a, 0, &result)){
    fprintf(stderr, "Dictionary: unit test 6.2 failing\n");
    errCode = -1;
  }
  if(Dictionary_find(b, 0, &result)){
    fprintf(stderr, "Dictionary: unit test 6.3 failing\n");
    errCode = -1;
  }
  // should succeed
  if(!Dictionary_find(a, 1, &result)){
    fprintf(stderr, "Dictionary: unit test 6.4 failing\n");
    errCode = -1;
  } else{
    if(result != &val1){
      fprintf(stderr, "Dictionary: unit test 6.5 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 10, &result)){
    fprintf(stderr, "Dictionary: unit test 6.6 failing\n");
    errCode = -1;
  } else{
    if(result != str1){
      fprintf(stderr, "Dictionary: unit test 6.7 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 2, &result)){
    fprintf(stderr, "Dictionary: unit test 6.8 failing\n");
    errCode = -1;
  } else{
    if(result != &val2){
      fprintf(stderr, "Dictionary: unit test 6.9 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 20, &result)){
    fprintf(stderr, "Dictionary: unit test 6.10 failing\n");
    errCode = -1;
  } else{
    if(result != str2){
      fprintf(stderr, "Dictionary: unit test 6.11 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 3, &result)){
    fprintf(stderr, "Dictionary: unit test 6.12 failing\n");
    errCode = -1;
  } else{
    if(result != &val3){
      fprintf(stderr, "Dictionary: unit test 6.13 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 30, &result)){
    fprintf(stderr, "Dictionary: unit test 6.14 failing\n");
    errCode = -1;
  } else{
    if(result != str3){
      fprintf(stderr, "Dictionary: unit test 6.15 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 4, &result)){
    fprintf(stderr, "Dictionary: unit test 6.16 failing\n");
    errCode = -1;
  } else{
    if(result != &val4){
      fprintf(stderr, "Dictionary: unit test 6.17 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 40, &result)){
    fprintf(stderr, "Dictionary: unit test 6.18 failing\n");
    errCode = -1;
  } else{
    if(result != str4){
      fprintf(stderr, "Dictionary: unit test 6.19 failing\n");
      errCode = -1;
    }
  }
  // fifth insert
  int val5 = 50;
  const char* str5 = "mno";
  
  Dictionary_insert(a, 5, &val5);
  Dictionary_insert(b, 50, str5);
 // should fail
  if(Dictionary_find(a, 0, &result)){
    fprintf(stderr, "Dictionary: unit test 7.2 failing\n");
    errCode = -1;
  }
  if(Dictionary_find(b, 0, &result)){
    fprintf(stderr, "Dictionary: unit test 7.3 failing\n");
    errCode = -1;
  }
  // should succeed
  if(!Dictionary_find(a, 1, &result)){
    fprintf(stderr, "Dictionary: unit test 7.4 failing\n");
    errCode = -1;
  } else{
    if(result != &val1){
      fprintf(stderr, "Dictionary: unit test 7.5 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 10, &result)){
    fprintf(stderr, "Dictionary: unit test 7.6 failing\n");
    errCode = -1;
  } else{
    if(result != str1){
      fprintf(stderr, "Dictionary: unit test 7.7 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 2, &result)){
    fprintf(stderr, "Dictionary: unit test 7.8 failing\n");
    errCode = -1;
  } else{
    if(result != &val2){
      fprintf(stderr, "Dictionary: unit test 7.9 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 20, &result)){
    fprintf(stderr, "Dictionary: unit test 7.10 failing\n");
    errCode = -1;
  } else{
    if(result != str2){
      fprintf(stderr, "Dictionary: unit test 7.11 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 3, &result)){
    fprintf(stderr, "Dictionary: unit test 7.12 failing\n");
    errCode = -1;
  } else{
    if(result != &val3){
      fprintf(stderr, "Dictionary: unit test 7.13 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 30, &result)){
    fprintf(stderr, "Dictionary: unit test 7.14 failing\n");
    errCode = -1;
  } else{
    if(result != str3){
      fprintf(stderr, "Dictionary: unit test 7.15 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 4, &result)){
    fprintf(stderr, "Dictionary: unit test 7.16 failing\n");
    errCode = -1;
  } else{
    if(result != &val4){
      fprintf(stderr, "Dictionary: unit test 7.17 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 40, &result)){
    fprintf(stderr, "Dictionary: unit test 7.18 failing\n");
    errCode = -1;
  } else{
    if(result != str4){
      fprintf(stderr, "Dictionary: unit test 7.19 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 5, &result)){
    fprintf(stderr, "Dictionary: unit test 7.20 failing\n");
    errCode = -1;
  } else{
    if(result != &val5){
      fprintf(stderr, "Dictionary: unit test 7.21 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 50, &result)){
    fprintf(stderr, "Dictionary: unit test 7.22 failing\n");
    errCode = -1;
  } else{
    if(result != str5){
      fprintf(stderr, "Dictionary: unit test 7.23 failing\n");
      errCode = -1;
    }
  }

  // sixth insert
  int val6 = 60;
  const char* str6 = "pqr";
  
  Dictionary_insert(a, 6, &val6);
  Dictionary_insert(b, 60, str6);
 // should fail
  if(Dictionary_find(a, 0, &result)){
    fprintf(stderr, "Dictionary: unit test 8.2 failing\n");
    errCode = -1;
  }
  if(Dictionary_find(b, 0, &result)){
    fprintf(stderr, "Dictionary: unit test 8.3 failing\n");
    errCode = -1;
  }
  // should succeed
  if(!Dictionary_find(a, 1, &result)){
    fprintf(stderr, "Dictionary: unit test 8.4 failing\n");
    errCode = -1;
  } else{
    if(result != &val1){
      fprintf(stderr, "Dictionary: unit test 8.5 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 10, &result)){
    fprintf(stderr, "Dictionary: unit test 8.6 failing\n");
    errCode = -1;
  } else{
    if(result != str1){
      fprintf(stderr, "Dictionary: unit test 8.7 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 2, &result)){
    fprintf(stderr, "Dictionary: unit test 8.8 failing\n");
    errCode = -1;
  } else{
    if(result != &val2){
      fprintf(stderr, "Dictionary: unit test 8.9 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 20, &result)){
    fprintf(stderr, "Dictionary: unit test 8.10 failing\n");
    errCode = -1;
  } else{
    if(result != str2){
      fprintf(stderr, "Dictionary: unit test 8.11 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 3, &result)){
    fprintf(stderr, "Dictionary: unit test 8.12 failing\n");
    errCode = -1;
  } else{
    if(result != &val3){
      fprintf(stderr, "Dictionary: unit test 8.13 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 30, &result)){
    fprintf(stderr, "Dictionary: unit test 8.14 failing\n");
    errCode = -1;
  } else{
    if(result != str3){
      fprintf(stderr, "Dictionary: unit test 8.15 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 4, &result)){
    fprintf(stderr, "Dictionary: unit test 8.16 failing\n");
    errCode = -1;
  } else{
    if(result != &val4){
      fprintf(stderr, "Dictionary: unit test 8.17 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 40, &result)){
    fprintf(stderr, "Dictionary: unit test 8.18 failing\n");
    errCode = -1;
  } else{
    if(result != str4){
      fprintf(stderr, "Dictionary: unit test 8.19 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 5, &result)){
    fprintf(stderr, "Dictionary: unit test 8.20 failing\n");
    errCode = -1;
  } else{
    if(result != &val5){
      fprintf(stderr, "Dictionary: unit test 8.21 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 50, &result)){
    fprintf(stderr, "Dictionary: unit test 8.22 failing\n");
    errCode = -1;
  } else{
    if(result != str5){
      fprintf(stderr, "Dictionary: unit test 8.23 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 6, &result)){
    fprintf(stderr, "Dictionary: unit test 8.24 failing\n");
    errCode = -1;
  } else{
    if(result != &val6){
      fprintf(stderr, "Dictionary: unit test 8.25 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 60, &result)){
    fprintf(stderr, "Dictionary: unit test 8.26 failing\n");
    errCode = -1;
  } else{
    if(result != str6){
      fprintf(stderr, "Dictionary: unit test 8.26 failing\n");
      errCode = -1;
    }
  }

  // seven insert
  int val7 = 70;
  const char* str7 = "stu";
  
  Dictionary_insert(a, 7, &val7);
  Dictionary_insert(b, 70, str7);
 // should fail
  if(Dictionary_find(a, 0, &result)){
    fprintf(stderr, "Dictionary: unit test 9.2 failing\n");
    errCode = -1;
  }
  if(Dictionary_find(b, 0, &result)){
    fprintf(stderr, "Dictionary: unit test 9.3 failing\n");
    errCode = -1;
  }
  // should succeed
  if(!Dictionary_find(a, 1, &result)){
    fprintf(stderr, "Dictionary: unit test 9.4 failing\n");
    errCode = -1;
  } else{
    if(result != &val1){
      fprintf(stderr, "Dictionary: unit test 9.5 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 10, &result)){
    fprintf(stderr, "Dictionary: unit test 9.6 failing\n");
    errCode = -1;
  } else{
    if(result != str1){
      fprintf(stderr, "Dictionary: unit test 9.7 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 2, &result)){
    fprintf(stderr, "Dictionary: unit test 9.8 failing\n");
    errCode = -1;
  } else{
    if(result != &val2){
      fprintf(stderr, "Dictionary: unit test 9.9 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 20, &result)){
    fprintf(stderr, "Dictionary: unit test 9.10 failing\n");
    errCode = -1;
  } else{
    if(result != str2){
      fprintf(stderr, "Dictionary: unit test 9.11 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 3, &result)){
    fprintf(stderr, "Dictionary: unit test 9.12 failing\n");
    errCode = -1;
  } else{
    if(result != &val3){
      fprintf(stderr, "Dictionary: unit test 9.13 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 30, &result)){
    fprintf(stderr, "Dictionary: unit test 9.14 failing\n");
    errCode = -1;
  } else{
    if(result != str3){
      fprintf(stderr, "Dictionary: unit test 9.15 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 4, &result)){
    fprintf(stderr, "Dictionary: unit test 9.16 failing\n");
    errCode = -1;
  } else{
    if(result != &val4){
      fprintf(stderr, "Dictionary: unit test 9.17 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 40, &result)){
    fprintf(stderr, "Dictionary: unit test 9.18 failing\n");
    errCode = -1;
  } else{
    if(result != str4){
      fprintf(stderr, "Dictionary: unit test 9.19 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 5, &result)){
    fprintf(stderr, "Dictionary: unit test 9.20 failing\n");
    errCode = -1;
  } else{
    if(result != &val5){
      fprintf(stderr, "Dictionary: unit test 9.21 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 50, &result)){
    fprintf(stderr, "Dictionary: unit test 9.22 failing\n");
    errCode = -1;
  } else{
    if(result != str5){
      fprintf(stderr, "Dictionary: unit test 9.23 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 6, &result)){
    fprintf(stderr, "Dictionary: unit test 9.24 failing\n");
    errCode = -1;
  } else{
    if(result != &val6){
      fprintf(stderr, "Dictionary: unit test 9.25 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 60, &result)){
    fprintf(stderr, "Dictionary: unit test 9.26 failing\n");
    errCode = -1;
  } else{
    if(result != str6){
      fprintf(stderr, "Dictionary: unit test 9.26 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 7, &result)){
    fprintf(stderr, "Dictionary: unit test 9.27 failing\n");
    errCode = -1;
  } else{
    if(result != &val7){
      fprintf(stderr, "Dictionary: unit test 9.28 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 70, &result)){
    fprintf(stderr, "Dictionary: unit test 9.29 failing\n");
    errCode = -1;
  } else{
    if(result != str7){
      fprintf(stderr, "Dictionary: unit test 9.30 failing\n");
      errCode = -1;
    }
  }
  // eighth insert
  int val8 = 80;
  const char* str8 = "vwx";
  
  Dictionary_insert(a, 8, &val8);
  Dictionary_insert(b, 80, str8);
 // should fail
  if(Dictionary_find(a, 0, &result)){
    fprintf(stderr, "Dictionary: unit test 10.2 failing\n");
    errCode = -1;
  }
  if(Dictionary_find(b, 0, &result)){
    fprintf(stderr, "Dictionary: unit test 10.3 failing\n");
    errCode = -1;
  }
  // should succeed
  if(!Dictionary_find(a, 1, &result)){
    fprintf(stderr, "Dictionary: unit test 10.4 failing\n");
    errCode = -1;
  } else{
    if(result != &val1){
      fprintf(stderr, "Dictionary: unit test 10.5 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 10, &result)){
    fprintf(stderr, "Dictionary: unit test 10.6 failing\n");
    errCode = -1;
  } else{
    if(result != str1){
      fprintf(stderr, "Dictionary: unit test 10.7 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 2, &result)){
    fprintf(stderr, "Dictionary: unit test 10.8 failing\n");
    errCode = -1;
  } else{
    if(result != &val2){
      fprintf(stderr, "Dictionary: unit test 10.9 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 20, &result)){
    fprintf(stderr, "Dictionary: unit test 10.10 failing\n");
    errCode = -1;
  } else{
    if(result != str2){
      fprintf(stderr, "Dictionary: unit test 10.11 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 3, &result)){
    fprintf(stderr, "Dictionary: unit test 10.12 failing\n");
    errCode = -1;
  } else{
    if(result != &val3){
      fprintf(stderr, "Dictionary: unit test 10.13 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 30, &result)){
    fprintf(stderr, "Dictionary: unit test 10.14 failing\n");
    errCode = -1;
  } else{
    if(result != str3){
      fprintf(stderr, "Dictionary: unit test 10.15 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 4, &result)){
    fprintf(stderr, "Dictionary: unit test 10.16 failing\n");
    errCode = -1;
  } else{
    if(result != &val4){
      fprintf(stderr, "Dictionary: unit test 10.17 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 40, &result)){
    fprintf(stderr, "Dictionary: unit test 10.18 failing\n");
    errCode = -1;
  } else{
    if(result != str4){
      fprintf(stderr, "Dictionary: unit test 10.19 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 5, &result)){
    fprintf(stderr, "Dictionary: unit test 10.20 failing\n");
    errCode = -1;
  } else{
    if(result != &val5){
      fprintf(stderr, "Dictionary: unit test 10.21 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 50, &result)){
    fprintf(stderr, "Dictionary: unit test 10.22 failing\n");
    errCode = -1;
  } else{
    if(result != str5){
      fprintf(stderr, "Dictionary: unit test 10.23 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 6, &result)){
    fprintf(stderr, "Dictionary: unit test 10.24 failing\n");
    errCode = -1;
  } else{
    if(result != &val6){
      fprintf(stderr, "Dictionary: unit test 10.25 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 60, &result)){
    fprintf(stderr, "Dictionary: unit test 10.26 failing\n");
    errCode = -1;
  } else{
    if(result != str6){
      fprintf(stderr, "Dictionary: unit test 10.26 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 7, &result)){
    fprintf(stderr, "Dictionary: unit test 10.27 failing\n");
    errCode = -1;
  } else{
    if(result != &val7){
      fprintf(stderr, "Dictionary: unit test 10.28 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 70, &result)){
    fprintf(stderr, "Dictionary: unit test 10.29 failing\n");
    errCode = -1;
  } else{
    if(result != str7){
      fprintf(stderr, "Dictionary: unit test 10.30 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 8, &result)){
    fprintf(stderr, "Dictionary: unit test 10.31 failing\n");
    errCode = -1;
  } else{
    if(result != &val8){
      fprintf(stderr, "Dictionary: unit test 10.32 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 80, &result)){
    fprintf(stderr, "Dictionary: unit test 10.33 failing\n");
    errCode = -1;
  } else{
    if(result != str8){
      fprintf(stderr, "Dictionary: unit test 10.34 failing\n");
      errCode = -1;
    }
  }
  // ninth insert
  int val9 = 90;
  const char* str9 = "vwx";
  
  Dictionary_insert(a, 9, &val9);
  Dictionary_insert(b, 90, str9);
 // should fail
  if(Dictionary_find(a, 0, &result)){
    fprintf(stderr, "Dictionary: unit test 11.2 failing\n");
    errCode = -1;
  }
  if(Dictionary_find(b, 0, &result)){
    fprintf(stderr, "Dictionary: unit test 11.3 failing\n");
    errCode = -1;
  }
  // should succeed
  if(!Dictionary_find(a, 1, &result)){
    fprintf(stderr, "Dictionary: unit test 11.4 failing\n");
    errCode = -1;
  } else{
    if(result != &val1){
      fprintf(stderr, "Dictionary: unit test 11.5 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 10, &result)){
    fprintf(stderr, "Dictionary: unit test 11.6 failing\n");
    errCode = -1;
  } else{
    if(result != str1){
      fprintf(stderr, "Dictionary: unit test 11.7 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 2, &result)){
    fprintf(stderr, "Dictionary: unit test 11.8 failing\n");
    errCode = -1;
  } else{
    if(result != &val2){
      fprintf(stderr, "Dictionary: unit test 11.9 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 20, &result)){
    fprintf(stderr, "Dictionary: unit test 11.10 failing\n");
    errCode = -1;
  } else{
    if(result != str2){
      fprintf(stderr, "Dictionary: unit test 11.11 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 3, &result)){
    fprintf(stderr, "Dictionary: unit test 11.12 failing\n");
    errCode = -1;
  } else{
    if(result != &val3){
      fprintf(stderr, "Dictionary: unit test 11.13 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 30, &result)){
    fprintf(stderr, "Dictionary: unit test 11.14 failing\n");
    errCode = -1;
  } else{
    if(result != str3){
      fprintf(stderr, "Dictionary: unit test 11.15 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 4, &result)){
    fprintf(stderr, "Dictionary: unit test 11.16 failing\n");
    errCode = -1;
  } else{
    if(result != &val4){
      fprintf(stderr, "Dictionary: unit test 11.17 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 40, &result)){
    fprintf(stderr, "Dictionary: unit test 11.18 failing\n");
    errCode = -1;
  } else{
    if(result != str4){
      fprintf(stderr, "Dictionary: unit test 11.19 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 5, &result)){
    fprintf(stderr, "Dictionary: unit test 11.20 failing\n");
    errCode = -1;
  } else{
    if(result != &val5){
      fprintf(stderr, "Dictionary: unit test 11.21 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 50, &result)){
    fprintf(stderr, "Dictionary: unit test 11.22 failing\n");
    errCode = -1;
  } else{
    if(result != str5){
      fprintf(stderr, "Dictionary: unit test 11.23 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 6, &result)){
    fprintf(stderr, "Dictionary: unit test 11.24 failing\n");
    errCode = -1;
  } else{
    if(result != &val6){
      fprintf(stderr, "Dictionary: unit test 11.25 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 60, &result)){
    fprintf(stderr, "Dictionary: unit test 11.26 failing\n");
    errCode = -1;
  } else{
    if(result != str6){
      fprintf(stderr, "Dictionary: unit test 11.26 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 7, &result)){
    fprintf(stderr, "Dictionary: unit test 11.27 failing\n");
    errCode = -1;
  } else{
    if(result != &val7){
      fprintf(stderr, "Dictionary: unit test 11.28 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 70, &result)){
    fprintf(stderr, "Dictionary: unit test 11.29 failing\n");
    errCode = -1;
  } else{
    if(result != str7){
      fprintf(stderr, "Dictionary: unit test 11.30 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 8, &result)){
    fprintf(stderr, "Dictionary: unit test 11.31 failing\n");
    errCode = -1;
  } else{
    if(result != &val8){
      fprintf(stderr, "Dictionary: unit test 11.32 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 80, &result)){
    fprintf(stderr, "Dictionary: unit test 11.33 failing\n");
    errCode = -1;
  } else{
    if(result != str8){
      fprintf(stderr, "Dictionary: unit test 11.34 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 9, &result)){
    fprintf(stderr, "Dictionary: unit test 11.35 failing\n");
    errCode = -1;
  } else{
    if(result != &val9){
      fprintf(stderr, "Dictionary: unit test 11.36 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 90, &result)){
    fprintf(stderr, "Dictionary: unit test 11.37 failing\n");
    errCode = -1;
  } else{
    if(result != str9){
      fprintf(stderr, "Dictionary: unit test 11.38 failing\n");
      errCode = -1;
    }
  }
  // tenth insert (duplicate keys)
  int val10 = 100;
  const char* str10 = "yz";
  
  Dictionary_insert(a, 1, &val10);
  Dictionary_insert(b, 10, str10);
 // should fail
  if(Dictionary_find(a, 0, &result)){
    fprintf(stderr, "Dictionary: unit test 12.2 failing\n");
    errCode = -1;
  }
  if(Dictionary_find(b, 0, &result)){
    fprintf(stderr, "Dictionary: unit test 12.3 failing\n");
    errCode = -1;
  }
  // should succeed
  if(!Dictionary_find(a, 1, &result)){
    fprintf(stderr, "Dictionary: unit test 12.4 failing\n");
    errCode = -1;
  } else{
    if(result != &val10){ // new value
      fprintf(stderr, "Dictionary: unit test 12.5 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 10, &result)){
    fprintf(stderr, "Dictionary: unit test 12.6 failing\n");
    errCode = -1;
  } else{
    if(result != str10){  // new value
      fprintf(stderr, "Dictionary: unit test 12.7 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 2, &result)){
    fprintf(stderr, "Dictionary: unit test 12.8 failing\n");
    errCode = -1;
  } else{
    if(result != &val2){
      fprintf(stderr, "Dictionary: unit test 12.9 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 20, &result)){
    fprintf(stderr, "Dictionary: unit test 12.10 failing\n");
    errCode = -1;
  } else{
    if(result != str2){
      fprintf(stderr, "Dictionary: unit test 12.11 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 3, &result)){
    fprintf(stderr, "Dictionary: unit test 12.12 failing\n");
    errCode = -1;
  } else{
    if(result != &val3){
      fprintf(stderr, "Dictionary: unit test 12.13 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 30, &result)){
    fprintf(stderr, "Dictionary: unit test 12.14 failing\n");
    errCode = -1;
  } else{
    if(result != str3){
      fprintf(stderr, "Dictionary: unit test 12.15 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 4, &result)){
    fprintf(stderr, "Dictionary: unit test 12.16 failing\n");
    errCode = -1;
  } else{
    if(result != &val4){
      fprintf(stderr, "Dictionary: unit test 12.17 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 40, &result)){
    fprintf(stderr, "Dictionary: unit test 12.18 failing\n");
    errCode = -1;
  } else{
    if(result != str4){
      fprintf(stderr, "Dictionary: unit test 12.19 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 5, &result)){
    fprintf(stderr, "Dictionary: unit test 12.20 failing\n");
    errCode = -1;
  } else{
    if(result != &val5){
      fprintf(stderr, "Dictionary: unit test 12.21 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 50, &result)){
    fprintf(stderr, "Dictionary: unit test 12.22 failing\n");
    errCode = -1;
  } else{
    if(result != str5){
      fprintf(stderr, "Dictionary: unit test 12.23 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 6, &result)){
    fprintf(stderr, "Dictionary: unit test 12.24 failing\n");
    errCode = -1;
  } else{
    if(result != &val6){
      fprintf(stderr, "Dictionary: unit test 12.25 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 60, &result)){
    fprintf(stderr, "Dictionary: unit test 12.26 failing\n");
    errCode = -1;
  } else{
    if(result != str6){
      fprintf(stderr, "Dictionary: unit test 12.26 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 7, &result)){
    fprintf(stderr, "Dictionary: unit test 12.27 failing\n");
    errCode = -1;
  } else{
    if(result != &val7){
      fprintf(stderr, "Dictionary: unit test 12.28 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 70, &result)){
    fprintf(stderr, "Dictionary: unit test 12.29 failing\n");
    errCode = -1;
  } else{
    if(result != str7){
      fprintf(stderr, "Dictionary: unit test 12.30 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 8, &result)){
    fprintf(stderr, "Dictionary: unit test 12.31 failing\n");
    errCode = -1;
  } else{
    if(result != &val8){
      fprintf(stderr, "Dictionary: unit test 12.32 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 80, &result)){
    fprintf(stderr, "Dictionary: unit test 12.33 failing\n");
    errCode = -1;
  } else{
    if(result != str8){
      fprintf(stderr, "Dictionary: unit test 12.34 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 9, &result)){
    fprintf(stderr, "Dictionary: unit test 12.35 failing\n");
    errCode = -1;
  } else{
    if(result != &val9){
      fprintf(stderr, "Dictionary: unit test 12.36 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 90, &result)){
    fprintf(stderr, "Dictionary: unit test 12.37 failing\n");
    errCode = -1;
  } else{
    if(result != str9){
      fprintf(stderr, "Dictionary: unit test 12.38 failing\n");
      errCode = -1;
    }
  }
  // first remove
  Dictionary_remove(a,1);
  Dictionary_remove(b,10);
  // should fail
  if(Dictionary_find(a, 1, &result)){
    fprintf(stderr, "Dictionary: unit test 13.2 failing\n");
    errCode = -1;
  }
  if(Dictionary_find(b, 10, &result)){
    fprintf(stderr, "Dictionary: unit test 13.3 failing\n");
    errCode = -1;
  }
  // should succeed
  if(!Dictionary_find(a, 2, &result)){
    fprintf(stderr, "Dictionary: unit test 13.8 failing\n");
    errCode = -1;
  } else{
    if(result != &val2){
      fprintf(stderr, "Dictionary: unit test 13.9 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 20, &result)){
    fprintf(stderr, "Dictionary: unit test 13.10 failing\n");
    errCode = -1;
  } else{
    if(result != str2){
      fprintf(stderr, "Dictionary: unit test 13.11 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 3, &result)){
    fprintf(stderr, "Dictionary: unit test 13.12 failing\n");
    errCode = -1;
  } else{
    if(result != &val3){
      fprintf(stderr, "Dictionary: unit test 13.13 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 30, &result)){
    fprintf(stderr, "Dictionary: unit test 13.14 failing\n");
    errCode = -1;
  } else{
    if(result != str3){
      fprintf(stderr, "Dictionary: unit test 13.15 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 4, &result)){
    fprintf(stderr, "Dictionary: unit test 13.16 failing\n");
    errCode = -1;
  } else{
    if(result != &val4){
      fprintf(stderr, "Dictionary: unit test 13.17 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 40, &result)){
    fprintf(stderr, "Dictionary: unit test 13.18 failing\n");
    errCode = -1;
  } else{
    if(result != str4){
      fprintf(stderr, "Dictionary: unit test 13.19 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 5, &result)){
    fprintf(stderr, "Dictionary: unit test 13.20 failing\n");
    errCode = -1;
  } else{
    if(result != &val5){
      fprintf(stderr, "Dictionary: unit test 13.21 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 50, &result)){
    fprintf(stderr, "Dictionary: unit test 13.22 failing\n");
    errCode = -1;
  } else{
    if(result != str5){
      fprintf(stderr, "Dictionary: unit test 13.23 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 6, &result)){
    fprintf(stderr, "Dictionary: unit test 13.24 failing\n");
    errCode = -1;
  } else{
    if(result != &val6){
      fprintf(stderr, "Dictionary: unit test 13.25 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 60, &result)){
    fprintf(stderr, "Dictionary: unit test 13.26 failing\n");
    errCode = -1;
  } else{
    if(result != str6){
      fprintf(stderr, "Dictionary: unit test 13.26 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 7, &result)){
    fprintf(stderr, "Dictionary: unit test 13.27 failing\n");
    errCode = -1;
  } else{
    if(result != &val7){
      fprintf(stderr, "Dictionary: unit test 13.28 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 70, &result)){
    fprintf(stderr, "Dictionary: unit test 13.29 failing\n");
    errCode = -1;
  } else{
    if(result != str7){
      fprintf(stderr, "Dictionary: unit test 13.30 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 8, &result)){
    fprintf(stderr, "Dictionary: unit test 13.31 failing\n");
    errCode = -1;
  } else{
    if(result != &val8){
      fprintf(stderr, "Dictionary: unit test 13.32 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 80, &result)){
    fprintf(stderr, "Dictionary: unit test 13.33 failing\n");
    errCode = -1;
  } else{
    if(result != str8){
      fprintf(stderr, "Dictionary: unit test 13.34 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 9, &result)){
    fprintf(stderr, "Dictionary: unit test 13.35 failing\n");
    errCode = -1;
  } else{
    if(result != &val9){
      fprintf(stderr, "Dictionary: unit test 13.36 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 90, &result)){
    fprintf(stderr, "Dictionary: unit test 13.37 failing\n");
    errCode = -1;
  } else{
    if(result != str9){
      fprintf(stderr, "Dictionary: unit test 13.38 failing\n");
      errCode = -1;
    }
  }
  // second remove
  Dictionary_remove(a,2);
  Dictionary_remove(b,20);
  // should fail
  if(Dictionary_find(a, 2, &result)){
    fprintf(stderr, "Dictionary: unit test 14.2 failing\n");
    errCode = -1;
  }
  if(Dictionary_find(b, 20, &result)){
    fprintf(stderr, "Dictionary: unit test 14.3 failing\n");
    errCode = -1;
  }
  // should succeed
 if(!Dictionary_find(a, 3, &result)){
    fprintf(stderr, "Dictionary: unit test 14.12 failing\n");
    errCode = -1;
  } else{
    if(result != &val3){
      fprintf(stderr, "Dictionary: unit test 14.13 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 30, &result)){
    fprintf(stderr, "Dictionary: unit test 14.14 failing\n");
    errCode = -1;
  } else{
    if(result != str3){
      fprintf(stderr, "Dictionary: unit test 14.15 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 4, &result)){
    fprintf(stderr, "Dictionary: unit test 14.16 failing\n");
    errCode = -1;
  } else{
    if(result != &val4){
      fprintf(stderr, "Dictionary: unit test 14.17 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 40, &result)){
    fprintf(stderr, "Dictionary: unit test 14.18 failing\n");
    errCode = -1;
  } else{
    if(result != str4){
      fprintf(stderr, "Dictionary: unit test 14.19 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 5, &result)){
    fprintf(stderr, "Dictionary: unit test 14.20 failing\n");
    errCode = -1;
  } else{
    if(result != &val5){
      fprintf(stderr, "Dictionary: unit test 14.21 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 50, &result)){
    fprintf(stderr, "Dictionary: unit test 14.22 failing\n");
    errCode = -1;
  } else{
    if(result != str5){
      fprintf(stderr, "Dictionary: unit test 14.23 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 6, &result)){
    fprintf(stderr, "Dictionary: unit test 14.24 failing\n");
    errCode = -1;
  } else{
    if(result != &val6){
      fprintf(stderr, "Dictionary: unit test 14.25 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 60, &result)){
    fprintf(stderr, "Dictionary: unit test 14.26 failing\n");
    errCode = -1;
  } else{
    if(result != str6){
      fprintf(stderr, "Dictionary: unit test 14.26 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 7, &result)){
    fprintf(stderr, "Dictionary: unit test 14.27 failing\n");
    errCode = -1;
  } else{
    if(result != &val7){
      fprintf(stderr, "Dictionary: unit test 14.28 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 70, &result)){
    fprintf(stderr, "Dictionary: unit test 14.29 failing\n");
    errCode = -1;
  } else{
    if(result != str7){
      fprintf(stderr, "Dictionary: unit test 14.30 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 8, &result)){
    fprintf(stderr, "Dictionary: unit test 14.31 failing\n");
    errCode = -1;
  } else{
    if(result != &val8){
      fprintf(stderr, "Dictionary: unit test 14.32 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 80, &result)){
    fprintf(stderr, "Dictionary: unit test 14.33 failing\n");
    errCode = -1;
  } else{
    if(result != str8){
      fprintf(stderr, "Dictionary: unit test 14.34 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 9, &result)){
    fprintf(stderr, "Dictionary: unit test 14.35 failing\n");
    errCode = -1;
  } else{
    if(result != &val9){
      fprintf(stderr, "Dictionary: unit test 14.36 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 90, &result)){
    fprintf(stderr, "Dictionary: unit test 14.37 failing\n");
    errCode = -1;
  } else{
    if(result != str9){
      fprintf(stderr, "Dictionary: unit test 14.38 failing\n");
      errCode = -1;
    }
  }
  // third remove
  Dictionary_remove(a,3);
  Dictionary_remove(b,30);
  // should fail
  if(Dictionary_find(a, 3, &result)){
    fprintf(stderr, "Dictionary: unit test 15.2 failing\n");
    errCode = -1;
  }
  if(Dictionary_find(b, 30, &result)){
    fprintf(stderr, "Dictionary: unit test 15.3 failing\n");
    errCode = -1;
  }
 if(!Dictionary_find(a, 4, &result)){
    fprintf(stderr, "Dictionary: unit test 15.16 failing\n");
    errCode = -1;
  } else{
    if(result != &val4){
      fprintf(stderr, "Dictionary: unit test 15.17 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 40, &result)){
    fprintf(stderr, "Dictionary: unit test 15.18 failing\n");
    errCode = -1;
  } else{
    if(result != str4){
      fprintf(stderr, "Dictionary: unit test 15.19 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 5, &result)){
    fprintf(stderr, "Dictionary: unit test 15.20 failing\n");
    errCode = -1;
  } else{
    if(result != &val5){
      fprintf(stderr, "Dictionary: unit test 15.21 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 50, &result)){
    fprintf(stderr, "Dictionary: unit test 15.22 failing\n");
    errCode = -1;
  } else{
    if(result != str5){
      fprintf(stderr, "Dictionary: unit test 15.23 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 6, &result)){
    fprintf(stderr, "Dictionary: unit test 15.24 failing\n");
    errCode = -1;
  } else{
    if(result != &val6){
      fprintf(stderr, "Dictionary: unit test 15.25 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 60, &result)){
    fprintf(stderr, "Dictionary: unit test 15.26 failing\n");
    errCode = -1;
  } else{
    if(result != str6){
      fprintf(stderr, "Dictionary: unit test 15.26 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 7, &result)){
    fprintf(stderr, "Dictionary: unit test 15.27 failing\n");
    errCode = -1;
  } else{
    if(result != &val7){
      fprintf(stderr, "Dictionary: unit test 15.28 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 70, &result)){
    fprintf(stderr, "Dictionary: unit test 15.29 failing\n");
    errCode = -1;
  } else{
    if(result != str7){
      fprintf(stderr, "Dictionary: unit test 15.30 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 8, &result)){
    fprintf(stderr, "Dictionary: unit test 15.31 failing\n");
    errCode = -1;
  } else{
    if(result != &val8){
      fprintf(stderr, "Dictionary: unit test 15.32 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 80, &result)){
    fprintf(stderr, "Dictionary: unit test 15.33 failing\n");
    errCode = -1;
  } else{
    if(result != str8){
      fprintf(stderr, "Dictionary: unit test 15.34 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 9, &result)){
    fprintf(stderr, "Dictionary: unit test 15.35 failing\n");
    errCode = -1;
  } else{
    if(result != &val9){
      fprintf(stderr, "Dictionary: unit test 15.36 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 90, &result)){
    fprintf(stderr, "Dictionary: unit test 15.37 failing\n");
    errCode = -1;
  } else{
    if(result != str9){
      fprintf(stderr, "Dictionary: unit test 15.38 failing\n");
      errCode = -1;
    }
  }
  // fourth remove
  Dictionary_remove(a,4);
  Dictionary_remove(b,40);
  // should fail
  if(Dictionary_find(a, 4, &result)){
    fprintf(stderr, "Dictionary: unit test 16.2 failing\n");
    errCode = -1;
  }
  if(Dictionary_find(b, 40, &result)){
    fprintf(stderr, "Dictionary: unit test 16.3 failing\n");
    errCode = -1;
  }
  if(!Dictionary_find(a, 5, &result)){
    fprintf(stderr, "Dictionary: unit test 16.20 failing\n");
    errCode = -1;
  } else{
    if(result != &val5){
      fprintf(stderr, "Dictionary: unit test 16.21 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 50, &result)){
    fprintf(stderr, "Dictionary: unit test 16.22 failing\n");
    errCode = -1;
  } else{
    if(result != str5){
      fprintf(stderr, "Dictionary: unit test 16.23 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 6, &result)){
    fprintf(stderr, "Dictionary: unit test 16.24 failing\n");
    errCode = -1;
  } else{
    if(result != &val6){
      fprintf(stderr, "Dictionary: unit test 16.25 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 60, &result)){
    fprintf(stderr, "Dictionary: unit test 16.26 failing\n");
    errCode = -1;
  } else{
    if(result != str6){
      fprintf(stderr, "Dictionary: unit test 16.26 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 7, &result)){
    fprintf(stderr, "Dictionary: unit test 16.27 failing\n");
    errCode = -1;
  } else{
    if(result != &val7){
      fprintf(stderr, "Dictionary: unit test 16.28 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 70, &result)){
    fprintf(stderr, "Dictionary: unit test 16.29 failing\n");
    errCode = -1;
  } else{
    if(result != str7){
      fprintf(stderr, "Dictionary: unit test 16.30 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 8, &result)){
    fprintf(stderr, "Dictionary: unit test 16.31 failing\n");
    errCode = -1;
  } else{
    if(result != &val8){
      fprintf(stderr, "Dictionary: unit test 16.32 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 80, &result)){
    fprintf(stderr, "Dictionary: unit test 16.33 failing\n");
    errCode = -1;
  } else{
    if(result != str8){
      fprintf(stderr, "Dictionary: unit test 16.34 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 9, &result)){
    fprintf(stderr, "Dictionary: unit test 16.35 failing\n");
    errCode = -1;
  } else{
    if(result != &val9){
      fprintf(stderr, "Dictionary: unit test 16.36 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 90, &result)){
    fprintf(stderr, "Dictionary: unit test 16.37 failing\n");
    errCode = -1;
  } else{
    if(result != str9){
      fprintf(stderr, "Dictionary: unit test 16.38 failing\n");
      errCode = -1;
    }
  }
  // fifth remove
  Dictionary_remove(a,5);
  Dictionary_remove(b,50);
  // should fail
  if(Dictionary_find(a, 5, &result)){
    fprintf(stderr, "Dictionary: unit test 17.2 failing\n");
    errCode = -1;
  }
  if(Dictionary_find(b, 50, &result)){
    fprintf(stderr, "Dictionary: unit test 17.3 failing\n");
    errCode = -1;
  }
  //should succeed
  if(!Dictionary_find(a, 6, &result)){
    fprintf(stderr, "Dictionary: unit test 17.24 failing\n");
    errCode = -1;
  } else{
    if(result != &val6){
      fprintf(stderr, "Dictionary: unit test 17.25 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 60, &result)){
    fprintf(stderr, "Dictionary: unit test 17.26 failing\n");
    errCode = -1;
  } else{
    if(result != str6){
      fprintf(stderr, "Dictionary: unit test 17.26 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 7, &result)){
    fprintf(stderr, "Dictionary: unit test 17.27 failing\n");
    errCode = -1;
  } else{
    if(result != &val7){
      fprintf(stderr, "Dictionary: unit test 17.28 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 70, &result)){
    fprintf(stderr, "Dictionary: unit test 17.29 failing\n");
    errCode = -1;
  } else{
    if(result != str7){
      fprintf(stderr, "Dictionary: unit test 17.30 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 8, &result)){
    fprintf(stderr, "Dictionary: unit test 17.31 failing\n");
    errCode = -1;
  } else{
    if(result != &val8){
      fprintf(stderr, "Dictionary: unit test 17.32 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 80, &result)){
    fprintf(stderr, "Dictionary: unit test 17.33 failing\n");
    errCode = -1;
  } else{
    if(result != str8){
      fprintf(stderr, "Dictionary: unit test 17.34 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 9, &result)){
    fprintf(stderr, "Dictionary: unit test 17.35 failing\n");
    errCode = -1;
  } else{
    if(result != &val9){
      fprintf(stderr, "Dictionary: unit test 17.36 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 90, &result)){
    fprintf(stderr, "Dictionary: unit test 17.37 failing\n");
    errCode = -1;
  } else{
    if(result != str9){
      fprintf(stderr, "Dictionary: unit test 17.38 failing\n");
      errCode = -1;
    }
  }
   // sixth remove
  Dictionary_remove(a,6);
  Dictionary_remove(b,60);
  // should fail
  if(Dictionary_find(a, 6, &result)){
    fprintf(stderr, "Dictionary: unit test 18.2 failing\n");
    errCode = -1;
  }
  if(Dictionary_find(b, 60, &result)){
    fprintf(stderr, "Dictionary: unit test 18.3 failing\n");
    errCode = -1;
  }
  //should succeed
  if(!Dictionary_find(a, 7, &result)){
    fprintf(stderr, "Dictionary: unit test 18.27 failing\n");
    errCode = -1;
  } else{
    if(result != &val7){
      fprintf(stderr, "Dictionary: unit test 18.28 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 70, &result)){
    fprintf(stderr, "Dictionary: unit test 18.29 failing\n");
    errCode = -1;
  } else{
    if(result != str7){
      fprintf(stderr, "Dictionary: unit test 18.30 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 8, &result)){
    fprintf(stderr, "Dictionary: unit test 18.31 failing\n");
    errCode = -1;
  } else{
    if(result != &val8){
      fprintf(stderr, "Dictionary: unit test 18.32 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 80, &result)){
    fprintf(stderr, "Dictionary: unit test 18.33 failing\n");
    errCode = -1;
  } else{
    if(result != str8){
      fprintf(stderr, "Dictionary: unit test 18.34 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 9, &result)){
    fprintf(stderr, "Dictionary: unit test 18.35 failing\n");
    errCode = -1;
  } else{
    if(result != &val9){
      fprintf(stderr, "Dictionary: unit test 18.36 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 90, &result)){
    fprintf(stderr, "Dictionary: unit test 18.37 failing\n");
    errCode = -1;
  } else{
    if(result != str9){
      fprintf(stderr, "Dictionary: unit test 18.38 failing\n");
      errCode = -1;
    }
  }
  // seventh remove
  Dictionary_remove(a,7);
  Dictionary_remove(b,70);
  // should fail
  if(Dictionary_find(a, 7, &result)){
    fprintf(stderr, "Dictionary: unit test 19.2 failing\n");
    errCode = -1;
  }
  if(Dictionary_find(b, 70, &result)){
    fprintf(stderr, "Dictionary: unit test 19.3 failing\n");
    errCode = -1;
  }
  //should succeed
  if(!Dictionary_find(a, 8, &result)){
    fprintf(stderr, "Dictionary: unit test 19.31 failing\n");
    errCode = -1;
  } else{
    if(result != &val8){
      fprintf(stderr, "Dictionary: unit test 19.32 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 80, &result)){
    fprintf(stderr, "Dictionary: unit test 19.33 failing\n");
    errCode = -1;
  } else{
    if(result != str8){
      fprintf(stderr, "Dictionary: unit test 19.34 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 9, &result)){
    fprintf(stderr, "Dictionary: unit test 19.35 failing\n");
    errCode = -1;
  } else{
    if(result != &val9){
      fprintf(stderr, "Dictionary: unit test 19.36 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 90, &result)){
    fprintf(stderr, "Dictionary: unit test 19.37 failing\n");
    errCode = -1;
  } else{
    if(result != str9){
      fprintf(stderr, "Dictionary: unit test 19.38 failing\n");
      errCode = -1;
    }
  }
  // seventh remove (redundant)
  Dictionary_remove(a,7);   
  Dictionary_remove(b,70);
  // should fail
  if(Dictionary_find(a, 7, &result)){
    fprintf(stderr, "Dictionary: unit test 20.2 failing\n");
    errCode = -1;
  }
  if(Dictionary_find(b, 70, &result)){
    fprintf(stderr, "Dictionary: unit test 20.3 failing\n");
    errCode = -1;
  }
  //should succeed
  if(!Dictionary_find(a, 8, &result)){
    fprintf(stderr, "Dictionary: unit test 20.31 failing\n");
    errCode = -1;
  } else{
    if(result != &val8){
      fprintf(stderr, "Dictionary: unit test 20.32 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 80, &result)){
    fprintf(stderr, "Dictionary: unit test 20.33 failing\n");
    errCode = -1;
  } else{
    if(result != str8){
      fprintf(stderr, "Dictionary: unit test 20.34 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(a, 9, &result)){
    fprintf(stderr, "Dictionary: unit test 20.35 failing\n");
    errCode = -1;
  } else{
    if(result != &val9){
      fprintf(stderr, "Dictionary: unit test 20.36 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 90, &result)){
    fprintf(stderr, "Dictionary: unit test 20.37 failing\n");
    errCode = -1;
  } else{
    if(result != str9){
      fprintf(stderr, "Dictionary: unit test 20.38 failing\n");
      errCode = -1;
    }
  }
  // eigth remove 
  Dictionary_remove(a,8);   
  Dictionary_remove(b,80);
  // should fail
  if(Dictionary_find(a, 8, &result)){
    fprintf(stderr, "Dictionary: unit test 21.0 failing\n");
    errCode = -1;
  }
  if(Dictionary_find(b, 80, &result)){
    fprintf(stderr, "Dictionary: unit test 21.1 failing\n");
    errCode = -1;
  }
  //should succeed
 if(!Dictionary_find(a, 9, &result)){
    fprintf(stderr, "Dictionary: unit test 21.2 failing\n");
    errCode = -1;
  } else{
    if(result != &val9){
      fprintf(stderr, "Dictionary: unit test 21.3 failing\n");
      errCode = -1;
    }
  }
  if(!Dictionary_find(b, 90, &result)){
    fprintf(stderr, "Dictionary: unit test 21.4 failing\n");
    errCode = -1;
  } else{
    if(result != str9){
      fprintf(stderr, "Dictionary: unit test 21.5 failing\n");
      errCode = -1;
    }
  }
  // nineth remove 
  Dictionary_remove(a,9);   
  Dictionary_remove(b,90);
  // should fail
  if(Dictionary_find(a, 9, &result)){
    fprintf(stderr, "Dictionary: unit test 22.0 failing\n");
    errCode = -1;
  }
  if(Dictionary_find(b, 90, &result)){
    fprintf(stderr, "Dictionary: unit test 22.1 failing\n");
    errCode = -1;
  }
  //should now be empty
  if(!Dictionary_isEmpty(a)){
    fprintf(stderr, "Dictionary: unit test 22.2 failing\n");
    errCode = -1;
  }
  if(!Dictionary_isEmpty(b)){
    fprintf(stderr, "Dictionary: unit test 22.3 failing\n");
    errCode = -1;
  }
  // multiple inserts and remove
#define DICT_T_C_SIMUL_SIZE 1024
  int values[DICT_T_C_SIMUL_SIZE];
  int i, j;
  int found;
  for(i = 0; i < DICT_T_C_SIMUL_SIZE; ++i){
    Dictionary_insert(a, i, &values[i]);
    for(j = 0; j <= i; ++j){
      int found = Dictionary_find(a, j, &result);  // should succeed for j <= i 
      if(!found){
        fprintf(stderr, 
            "Dictionary: unit test 23.0 failing for (i,j) = (%d,%d)\n",i,j);
        errCode = -1;
      } else {
        if(result != &values[j]){
          fprintf(stderr, 
            "Dictionary: unit test 23.1 failing for (i,j) = (%d,%d)\n",i,j);
        }
      }
    }
    for(j = i+1; j < DICT_T_C_SIMUL_SIZE; ++j){
      int found = Dictionary_find(a, j, &result);  // should fail for i < j 
      if(found){
        fprintf(stderr, 
          "Dictionary: unit test 23.2 failing for (i,j) = (%d,%d)\n",i,j);
         errCode = -1;
      }
    }
  }
  for(i = 0; i < DICT_T_C_SIMUL_SIZE; ++i){
    Dictionary_remove(a, i);
    for(j = 0; j <= i; ++j){
      int found = Dictionary_find(a, j, &result);  // should fail for j <= i 
      if(found){
        fprintf(stderr, 
          "Dictionary: unit test 23.3 failing for (i,j) = (%d,%d)\n",i,j);
         errCode = -1;
      }
    }
    for(j = i+1; j < DICT_T_C_SIMUL_SIZE; ++j){
      int found = Dictionary_find(a, j, &result);  // should succeed for i < j 
      if(!found){
        fprintf(stderr, 
            "Dictionary: unit test 23.4 failing for (i,j) = (%d,%d)\n",i,j);
        errCode = -1;
      } else {
        if(result != &values[j]){
          fprintf(stderr, 
            "Dictionary: unit test 23.5 failing for (i,j) = (%d,%d)\n",i,j);
        }
      }
    }
  }



//  Dictionary_debug(a);
//  Dictionary_debug(b);

  Dictionary_delete(a);
  Dictionary_delete(b);
  // final memory leak test
  if(Dictionary_hasMemoryLeak()){
    fprintf(stderr,"Dictionary: memory leak detected\n");
    errCode = -1;
  }
  if(Link_hasMemoryLeak()){
    fprintf(stderr, "Dictionary: memory leak detected for Link\n");
  }
 fprintf(stderr, "Dictionary: unit test complete\n");  
  return errCode;
}


int main(){
  return dictionary_test();
}
