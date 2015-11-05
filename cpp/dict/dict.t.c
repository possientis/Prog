// dict.t.c
#ifndef INCLUDED_DICT
#include "dict.h"
#endif

#include <stdio.h>
#include <string>

static void printInt(const void* ptr){

  int i = *(int*) ptr;
  printf("%d",i);

}

static void printStr(const void* ptr){

  std::string s = *(std::string*) ptr;

  printf("%s",s.c_str());

}


static int dict_test();

int main(int argc, char* argv[]){

  return dict_test();

}

static int dict_test(){

  printf("Dictionary: starting unit test\n");

  int k0 = 0;
  int k1 = 1;
  int k2 = 2;
  int k3 = 3;
  int k4 = 4;
  int k5 = 5;
  int k6 = 6;
  int k7 = 7;
  int k8 = 8;
  int k9 = 9;
  int k11 = 1;  // duplicate key

  int v1 = 10;
  int v2 = 20;
  int v3 = 30;
  int v4 = 40;
  int v5 = 50;
  int v6 = 60;
  int v7 = 70;
  int v8 = 80;
  int v9 = 90;
  int v11 = 11;

  const std::string s0 = "abd";
  const std::string s1 = "abc";
  const std::string s2 = "def";
  const std::string s3 = "hij";
  const std::string s4 = "klm";
  const std::string s5 = "nop";
  const std::string s6 = "qrs";
  const std::string s7 = "tuv";
  const std::string s8 = "wxy";
  const std::string s9 = "zab";
  const std::string s11 = "abc";  // duplicate key

  int w1 = 100;
  int w2 = 200;
  int w3 = 300;
  int w4 = 400;
  int w5 = 500;
  int w6 = 600;
  int w7 = 700;
  int w8 = 800;
  int w9 = 900;
  int w11 = 110;


  Dictionary<int> a;  // integer keys
  Dictionary<std::string> b;  // string keys

  // first insert
  a.insert(k1,&v1);
  b.insert(s1,&w1);
  if(!a.isCheckOk()) printf("Dictionary: unit test 1 failing\n");
  if(!b.isCheckOk()) printf("Dictionary: unit test 2 failing\n");
  // search should fail
  if(a.find(k0) != nullptr) printf("Dictionary: unit test 3 failing\n");
  if(b.find(s0) != nullptr) printf("Dictionary: unit test 4 failing\n");
  // search should succeed
  if(a.find(k1) != &v1) printf("Dictionary: unit test 5 failing\n");
  if(b.find(s1) != &w1) printf("Dictionary: unit test 6 failing\n");
 // second insert
  a.insert(k2,&v2);
  b.insert(s2,&w2);
  if(!a.isCheckOk()) printf("Dictionary: unit test 7 failing\n");
  if(!b.isCheckOk()) printf("Dictionary: unit test 8 failing\n");
  // search should fail
  if(a.find(k0) != nullptr) printf("Dictionary: unit test 9 failing\n");
  if(b.find(s0) != nullptr) printf("Dictionary: unit test 10 failing\n");
  // search should succeed
  if(a.find(k1) != &v1) printf("Dictionary: unit test 11 failing\n");
  if(b.find(s1) != &w1) printf("Dictionary: unit test 12 failing\n");
  if(a.find(k2) != &v2) printf("Dictionary: unit test 13 failing\n");
  if(b.find(s2) != &w2) printf("Dictionary: unit test 14 failing\n");
  // third insert
  a.insert(k3,&v3);
  b.insert(s3,&w3);
  if(!a.isCheckOk()) printf("Dictionary: unit test 15 failing\n");
  if(!b.isCheckOk()) printf("Dictionary: unit test 16 failing\n");
  // search should fail
  if(a.find(k0) != nullptr) printf("Dictionary: unit test 17 failing\n");
  if(b.find(s0) != nullptr) printf("Dictionary: unit test 18 failing\n");
  // search should succeed
  if(a.find(k1) != &v1) printf("Dictionary: unit test 19 failing\n");
  if(b.find(s1) != &w1) printf("Dictionary: unit test 20 failing\n");
  if(a.find(k2) != &v2) printf("Dictionary: unit test 21 failing\n");
  if(b.find(s2) != &w2) printf("Dictionary: unit test 22 failing\n");
  if(a.find(k3) != &v3) printf("Dictionary: unit test 23 failing\n");
  if(b.find(s3) != &w3) printf("Dictionary: unit test 24 failing\n");
  // fourth insert
  a.insert(k4,&v4);
  b.insert(s4,&w4);
  if(!a.isCheckOk()) printf("Dictionary: unit test 25 failing\n");
  if(!b.isCheckOk()) printf("Dictionary: unit test 26 failing\n");
  // search should fail
  if(a.find(k0) != nullptr) printf("Dictionary: unit test 27 failing\n");
  if(b.find(s0) != nullptr) printf("Dictionary: unit test 28 failing\n");
  // search should succeed
  if(a.find(k1) != &v1) printf("Dictionary: unit test 29 failing\n");
  if(b.find(s1) != &w1) printf("Dictionary: unit test 30 failing\n");
  if(a.find(k2) != &v2) printf("Dictionary: unit test 31 failing\n");
  if(b.find(s2) != &w2) printf("Dictionary: unit test 32 failing\n");
  if(a.find(k3) != &v3) printf("Dictionary: unit test 33 failing\n");
  if(b.find(s3) != &w3) printf("Dictionary: unit test 34 failing\n");
  if(a.find(k4) != &v4) printf("Dictionary: unit test 35 failing\n");
  if(b.find(s4) != &w4) printf("Dictionary: unit test 36 failing\n");
  // fifth insert
  a.insert(k5,&v5);
  b.insert(s5,&w5);
  if(!a.isCheckOk()) printf("Dictionary: unit test 37 failing\n");
  if(!b.isCheckOk()) printf("Dictionary: unit test 38 failing\n");
  // search should fail
  if(a.find(k0) != nullptr) printf("Dictionary: unit test 39 failing\n");
  if(b.find(s0) != nullptr) printf("Dictionary: unit test 40 failing\n");
  // search should succeed
  if(a.find(k1) != &v1) printf("Dictionary: unit test 41 failing\n");
  if(b.find(s1) != &w1) printf("Dictionary: unit test 42 failing\n");
  if(a.find(k2) != &v2) printf("Dictionary: unit test 43 failing\n");
  if(b.find(s2) != &w2) printf("Dictionary: unit test 44 failing\n");
  if(a.find(k3) != &v3) printf("Dictionary: unit test 45 failing\n");
  if(b.find(s3) != &w3) printf("Dictionary: unit test 46 failing\n");
  if(a.find(k4) != &v4) printf("Dictionary: unit test 47 failing\n");
  if(b.find(s4) != &w4) printf("Dictionary: unit test 48 failing\n");
  if(a.find(k5) != &v5) printf("Dictionary: unit test 49 failing\n");
  if(b.find(s5) != &w5) printf("Dictionary: unit test 50 failing\n");
  // sixth insert
  a.insert(k6,&v6);
  b.insert(s6,&w6);
  if(!a.isCheckOk()) printf("Dictionary: unit test 51 failing\n");
  if(!b.isCheckOk()) printf("Dictionary: unit test 52 failing\n");
  // search should fail
  if(a.find(k0) != nullptr) printf("Dictionary: unit test 53 failing\n");
  if(b.find(s0) != nullptr) printf("Dictionary: unit test 54 failing\n");
  // search should succeed
  if(a.find(k1) != &v1) printf("Dictionary: unit test 55 failing\n");
  if(b.find(s1) != &w1) printf("Dictionary: unit test 56 failing\n");
  if(a.find(k2) != &v2) printf("Dictionary: unit test 57 failing\n");
  if(b.find(s2) != &w2) printf("Dictionary: unit test 58 failing\n");
  if(a.find(k3) != &v3) printf("Dictionary: unit test 59 failing\n");
  if(b.find(s3) != &w3) printf("Dictionary: unit test 60 failing\n");
  if(a.find(k4) != &v4) printf("Dictionary: unit test 61 failing\n");
  if(b.find(s4) != &w4) printf("Dictionary: unit test 62 failing\n");
  if(a.find(k5) != &v5) printf("Dictionary: unit test 63 failing\n");
  if(b.find(s5) != &w5) printf("Dictionary: unit test 64 failing\n");
  if(a.find(k6) != &v6) printf("Dictionary: unit test 65 failing\n");
  if(b.find(s6) != &w6) printf("Dictionary: unit test 66 failing\n");
  // seventh insert
  a.insert(k7,&v7);
  b.insert(s7,&w7);
  if(!a.isCheckOk()) printf("Dictionary: unit test 67 failing\n");
  if(!b.isCheckOk()) printf("Dictionary: unit test 68 failing\n");
  // search should fail
  if(a.find(k0) != nullptr) printf("Dictionary: unit test 69 failing\n");
  if(b.find(s0) != nullptr) printf("Dictionary: unit test 70 failing\n");
  // search should succeed
  if(a.find(k1) != &v1) printf("Dictionary: unit test 71 failing\n");
  if(b.find(s1) != &w1) printf("Dictionary: unit test 72 failing\n");
  if(a.find(k2) != &v2) printf("Dictionary: unit test 73 failing\n");
  if(b.find(s2) != &w2) printf("Dictionary: unit test 74 failing\n");
  if(a.find(k3) != &v3) printf("Dictionary: unit test 75 failing\n");
  if(b.find(s3) != &w3) printf("Dictionary: unit test 76 failing\n");
  if(a.find(k4) != &v4) printf("Dictionary: unit test 77 failing\n");
  if(b.find(s4) != &w4) printf("Dictionary: unit test 78 failing\n");
  if(a.find(k5) != &v5) printf("Dictionary: unit test 79 failing\n");
  if(b.find(s5) != &w5) printf("Dictionary: unit test 80 failing\n");
  if(a.find(k6) != &v6) printf("Dictionary: unit test 81 failing\n");
  if(b.find(s6) != &w6) printf("Dictionary: unit test 82 failing\n");
  if(a.find(k7) != &v7) printf("Dictionary: unit test 83 failing\n");
  if(b.find(s7) != &w7) printf("Dictionary: unit test 84 failing\n");
  // eighth insert
  a.insert(k8,&v8);
  b.insert(s8,&w8);
  if(!a.isCheckOk()) printf("Dictionary: unit test 85 failing\n");
  if(!b.isCheckOk()) printf("Dictionary: unit test 86 failing\n");
  // search should fail
  if(a.find(k0) != nullptr) printf("Dictionary: unit test 87 failing\n");
  if(b.find(s0) != nullptr) printf("Dictionary: unit test 88 failing\n");
  // search should succeed
  if(a.find(k1) != &v1) printf("Dictionary: unit test 89 failing\n");
  if(b.find(s1) != &w1) printf("Dictionary: unit test 90 failing\n");
  if(a.find(k2) != &v2) printf("Dictionary: unit test 91 failing\n");
  if(b.find(s2) != &w2) printf("Dictionary: unit test 92 failing\n");
  if(a.find(k3) != &v3) printf("Dictionary: unit test 93 failing\n");
  if(b.find(s3) != &w3) printf("Dictionary: unit test 94 failing\n");
  if(a.find(k4) != &v4) printf("Dictionary: unit test 95 failing\n");
  if(b.find(s4) != &w4) printf("Dictionary: unit test 96 failing\n");
  if(a.find(k5) != &v5) printf("Dictionary: unit test 97 failing\n");
  if(b.find(s5) != &w5) printf("Dictionary: unit test 98 failing\n");
  if(a.find(k6) != &v6) printf("Dictionary: unit test 99 failing\n");
  if(b.find(s6) != &w6) printf("Dictionary: unit test 100 failing\n");
  if(a.find(k7) != &v7) printf("Dictionary: unit test 101 failing\n");
  if(b.find(s7) != &w7) printf("Dictionary: unit test 102 failing\n");
  if(a.find(k8) != &v8) printf("Dictionary: unit test 103 failing\n");
  if(b.find(s8) != &w8) printf("Dictionary: unit test 104 failing\n");
  // ninth insert
  a.insert(k9,&v9);
  b.insert(s9,&w9);
  if(!a.isCheckOk()) printf("Dictionary: unit test 105 failing\n");
  if(!b.isCheckOk()) printf("Dictionary: unit test 106 failing\n");
  // search should fail
  if(a.find(k0) != nullptr) printf("Dictionary: unit test 107 failing\n");
  if(b.find(s0) != nullptr) printf("Dictionary: unit test 108 failing\n");
  // search should succeed
  if(a.find(k1) != &v1) printf("Dictionary: unit test 109 failing\n");
  if(b.find(s1) != &w1) printf("Dictionary: unit test 110 failing\n");
  if(a.find(k2) != &v2) printf("Dictionary: unit test 111 failing\n");
  if(b.find(s2) != &w2) printf("Dictionary: unit test 112 failing\n");
  if(a.find(k3) != &v3) printf("Dictionary: unit test 113 failing\n");
  if(b.find(s3) != &w3) printf("Dictionary: unit test 114 failing\n");
  if(a.find(k4) != &v4) printf("Dictionary: unit test 115 failing\n");
  if(b.find(s4) != &w4) printf("Dictionary: unit test 116 failing\n");
  if(a.find(k5) != &v5) printf("Dictionary: unit test 117 failing\n");
  if(b.find(s5) != &w5) printf("Dictionary: unit test 118 failing\n");
  if(a.find(k6) != &v6) printf("Dictionary: unit test 119 failing\n");
  if(b.find(s6) != &w6) printf("Dictionary: unit test 120 failing\n");
  if(a.find(k7) != &v7) printf("Dictionary: unit test 121 failing\n");
  if(b.find(s7) != &w7) printf("Dictionary: unit test 122 failing\n");
  if(a.find(k8) != &v8) printf("Dictionary: unit test 123 failing\n");
  if(b.find(s8) != &w8) printf("Dictionary: unit test 124 failing\n");
  if(a.find(k9) != &v9) printf("Dictionary: unit test 125 failing\n");
  if(b.find(s9) != &w9) printf("Dictionary: unit test 126 failing\n");
  // insert of duplicate keys
  a.insert(k11,&v11);   // same key as k1
  b.insert(s11,&w11);   // same key as s1
  if(!a.isCheckOk()) printf("Dictionary: unit test 127 failing\n");
  if(!b.isCheckOk()) printf("Dictionary: unit test 128 failing\n");
  // search should fail
  if(a.find(k0) != nullptr) printf("Dictionary: unit test 129 failing\n");
  if(b.find(s0) != nullptr) printf("Dictionary: unit test 130 failing\n");
  // search should succeed
  if(a.find(k1) != &v11) printf("Dictionary: unit test 131 failing\n");
  if(b.find(s1) != &w11) printf("Dictionary: unit test 132 failing\n");
  if(a.find(k2) != &v2) printf("Dictionary: unit test 133 failing\n");
  if(b.find(s2) != &w2) printf("Dictionary: unit test 134 failing\n");
  if(a.find(k3) != &v3) printf("Dictionary: unit test 135 failing\n");
  if(b.find(s3) != &w3) printf("Dictionary: unit test 136 failing\n");
  if(a.find(k4) != &v4) printf("Dictionary: unit test 137 failing\n");
  if(b.find(s4) != &w4) printf("Dictionary: unit test 138 failing\n");
  if(a.find(k5) != &v5) printf("Dictionary: unit test 139 failing\n");
  if(b.find(s5) != &w5) printf("Dictionary: unit test 140 failing\n");
  if(a.find(k6) != &v6) printf("Dictionary: unit test 141 failing\n");
  if(b.find(s6) != &w6) printf("Dictionary: unit test 142 failing\n");
  if(a.find(k7) != &v7) printf("Dictionary: unit test 143 failing\n");
  if(b.find(s7) != &w7) printf("Dictionary: unit test 144 failing\n");
  if(a.find(k8) != &v8) printf("Dictionary: unit test 145 failing\n");
  if(b.find(s8) != &w8) printf("Dictionary: unit test 146 failing\n");
  if(a.find(k9) != &v9) printf("Dictionary: unit test 147 failing\n");
  if(b.find(s9) != &w9) printf("Dictionary: unit test 148 failing\n");
  // first delete
  a.del(k1);
  b.del(s1);
  if(!a.isCheckOk()) printf("Dictionary: unit test 149 failing\n");
  if(!b.isCheckOk()) printf("Dictionary: unit test 150 failing\n");
  // search should fail
  if(a.find(k1) != nullptr) printf("Dictionary: unit test 151 failing\n");
  if(b.find(s1) != nullptr) printf("Dictionary: unit test 152 failing\n");
  // search should succeed
  if(a.find(k2) != &v2) printf("Dictionary: unit test 153 failing\n");
  if(b.find(s2) != &w2) printf("Dictionary: unit test 154 failing\n");
  if(a.find(k3) != &v3) printf("Dictionary: unit test 155 failing\n");
  if(b.find(s3) != &w3) printf("Dictionary: unit test 156 failing\n");
  if(a.find(k4) != &v4) printf("Dictionary: unit test 157 failing\n");
  if(b.find(s4) != &w4) printf("Dictionary: unit test 158 failing\n");
  if(a.find(k5) != &v5) printf("Dictionary: unit test 159 failing\n");
  if(b.find(s5) != &w5) printf("Dictionary: unit test 160 failing\n");
  if(a.find(k6) != &v6) printf("Dictionary: unit test 161 failing\n");
  if(b.find(s6) != &w6) printf("Dictionary: unit test 162 failing\n");
  if(a.find(k7) != &v7) printf("Dictionary: unit test 163 failing\n");
  if(b.find(s7) != &w7) printf("Dictionary: unit test 164 failing\n");
  if(a.find(k8) != &v8) printf("Dictionary: unit test 165 failing\n");
  if(b.find(s8) != &w8) printf("Dictionary: unit test 166 failing\n");
  if(a.find(k9) != &v9) printf("Dictionary: unit test 167 failing\n");
  if(b.find(s9) != &w9) printf("Dictionary: unit test 168 failing\n");
  // second delete
  a.del(k2);
  b.del(s2);
  if(!a.isCheckOk()) printf("Dictionary: unit test 169 failing\n");
  if(!b.isCheckOk()) printf("Dictionary: unit test 170 failing\n");
  // search should fail
  if(a.find(k2) != nullptr) printf("Dictionary: unit test 171 failing\n");
  if(b.find(s2) != nullptr) printf("Dictionary: unit test 172 failing\n");
  // search should succeed
  if(a.find(k3) != &v3) printf("Dictionary: unit test 173 failing\n");
  if(b.find(s3) != &w3) printf("Dictionary: unit test 174 failing\n");
  if(a.find(k4) != &v4) printf("Dictionary: unit test 175 failing\n");
  if(b.find(s4) != &w4) printf("Dictionary: unit test 176 failing\n");
  if(a.find(k5) != &v5) printf("Dictionary: unit test 177 failing\n");
  if(b.find(s5) != &w5) printf("Dictionary: unit test 178 failing\n");
  if(a.find(k6) != &v6) printf("Dictionary: unit test 179 failing\n");
  if(b.find(s6) != &w6) printf("Dictionary: unit test 180 failing\n");
  if(a.find(k7) != &v7) printf("Dictionary: unit test 181 failing\n");
  if(b.find(s7) != &w7) printf("Dictionary: unit test 182 failing\n");
  if(a.find(k8) != &v8) printf("Dictionary: unit test 183 failing\n");
  if(b.find(s8) != &w8) printf("Dictionary: unit test 184 failing\n");
  if(a.find(k9) != &v9) printf("Dictionary: unit test 185 failing\n");
  if(b.find(s9) != &w9) printf("Dictionary: unit test 186 failing\n");
  // third delete
  a.del(k3);
  b.del(s3);
  if(!a.isCheckOk()) printf("Dictionary: unit test 187 failing\n");
  if(!b.isCheckOk()) printf("Dictionary: unit test 188 failing\n");
  // search should fail
  if(a.find(k3) != nullptr) printf("Dictionary: unit test 189 failing\n");
  if(b.find(s3) != nullptr) printf("Dictionary: unit test 190 failing\n");
  // search should succeed
  if(a.find(k4) != &v4) printf("Dictionary: unit test 191 failing\n");
  if(b.find(s4) != &w4) printf("Dictionary: unit test 192 failing\n");
  if(a.find(k5) != &v5) printf("Dictionary: unit test 193 failing\n");
  if(b.find(s5) != &w5) printf("Dictionary: unit test 194 failing\n");
  if(a.find(k6) != &v6) printf("Dictionary: unit test 195 failing\n");
  if(b.find(s6) != &w6) printf("Dictionary: unit test 196 failing\n");
  if(a.find(k7) != &v7) printf("Dictionary: unit test 197 failing\n");
  if(b.find(s7) != &w7) printf("Dictionary: unit test 198 failing\n");
  if(a.find(k8) != &v8) printf("Dictionary: unit test 199 failing\n");
  if(b.find(s8) != &w8) printf("Dictionary: unit test 200 failing\n");
  if(a.find(k9) != &v9) printf("Dictionary: unit test 201 failing\n");
  if(b.find(s9) != &w9) printf("Dictionary: unit test 202 failing\n");
  // fourth delete
  a.del(k4);
  b.del(s4);
  if(!a.isCheckOk()) printf("Dictionary: unit test 203 failing\n");
  if(!b.isCheckOk()) printf("Dictionary: unit test 204 failing\n");
  // search should fail
  if(a.find(k4) != nullptr) printf("Dictionary: unit test 205 failing\n");
  if(b.find(s4) != nullptr) printf("Dictionary: unit test 206 failing\n");
  // search should succeed
  if(a.find(k5) != &v5) printf("Dictionary: unit test 207 failing\n");
  if(b.find(s5) != &w5) printf("Dictionary: unit test 208 failing\n");
  if(a.find(k6) != &v6) printf("Dictionary: unit test 209 failing\n");
  if(b.find(s6) != &w6) printf("Dictionary: unit test 210 failing\n");
  if(a.find(k7) != &v7) printf("Dictionary: unit test 211 failing\n");
  if(b.find(s7) != &w7) printf("Dictionary: unit test 212 failing\n");
  if(a.find(k8) != &v8) printf("Dictionary: unit test 213 failing\n");
  if(b.find(s8) != &w8) printf("Dictionary: unit test 214 failing\n");
  if(a.find(k9) != &v9) printf("Dictionary: unit test 215 failing\n");
  if(b.find(s9) != &w9) printf("Dictionary: unit test 216 failing\n");
  // fifth delete
  a.del(k5);
  b.del(s5);
  if(!a.isCheckOk()) printf("Dictionary: unit test 217 failing\n");
  if(!b.isCheckOk()) printf("Dictionary: unit test 218 failing\n");
  // search should fail
  if(a.find(k5) != nullptr) printf("Dictionary: unit test 219 failing\n");
  if(b.find(s5) != nullptr) printf("Dictionary: unit test 220 failing\n");
  // search should succeed
  if(a.find(k6) != &v6) printf("Dictionary: unit test 221 failing\n");
  if(b.find(s6) != &w6) printf("Dictionary: unit test 222 failing\n");
  if(a.find(k7) != &v7) printf("Dictionary: unit test 223 failing\n");
  if(b.find(s7) != &w7) printf("Dictionary: unit test 224 failing\n");
  if(a.find(k8) != &v8) printf("Dictionary: unit test 225 failing\n");
  if(b.find(s8) != &w8) printf("Dictionary: unit test 226 failing\n");
  if(a.find(k9) != &v9) printf("Dictionary: unit test 227 failing\n");
  if(b.find(s9) != &w9) printf("Dictionary: unit test 228 failing\n");
  // sixth delete
  a.del(k6);
  b.del(s6);
  if(!a.isCheckOk()) printf("Dictionary: unit test 229 failing\n");
  if(!b.isCheckOk()) printf("Dictionary: unit test 230 failing\n");
  // search should fail
  if(a.find(k6) != nullptr) printf("Dictionary: unit test 231 failing\n");
  if(b.find(s6) != nullptr) printf("Dictionary: unit test 232 failing\n");
  // search should succeed
  if(a.find(k7) != &v7) printf("Dictionary: unit test 233 failing\n");
  if(b.find(s7) != &w7) printf("Dictionary: unit test 234 failing\n");
  if(a.find(k8) != &v8) printf("Dictionary: unit test 235 failing\n");
  if(b.find(s8) != &w8) printf("Dictionary: unit test 236 failing\n");
  if(a.find(k9) != &v9) printf("Dictionary: unit test 237 failing\n");
  if(b.find(s9) != &w9) printf("Dictionary: unit test 238 failing\n");
  // seventh delete
  a.del(k7);
  b.del(s7);
  if(!a.isCheckOk()) printf("Dictionary: unit test 239 failing\n");
  if(!b.isCheckOk()) printf("Dictionary: unit test 240 failing\n");
  // search should fail
  if(a.find(k7) != nullptr) printf("Dictionary: unit test 241 failing\n");
  if(b.find(s7) != nullptr) printf("Dictionary: unit test 242 failing\n");
  // search should succeed
  if(a.find(k8) != &v8) printf("Dictionary: unit test 243 failing\n");
  if(b.find(s8) != &w8) printf("Dictionary: unit test 244 failing\n");
  if(a.find(k9) != &v9) printf("Dictionary: unit test 245 failing\n");
  if(b.find(s9) != &w9) printf("Dictionary: unit test 246 failing\n");
  // redundant delete
  a.del(k7);
  b.del(s7);
  if(!a.isCheckOk()) printf("Dictionary: unit test 247 failing\n");
  if(!b.isCheckOk()) printf("Dictionary: unit test 248 failing\n");
  // search should fail
  if(a.find(k7) != nullptr) printf("Dictionary: unit test 249 failing\n");
  if(b.find(s7) != nullptr) printf("Dictionary: unit test 250 failing\n");
  // search should succeed
  if(a.find(k8) != &v8) printf("Dictionary: unit test 251 failing\n");
  if(b.find(s8) != &w8) printf("Dictionary: unit test 252 failing\n");
  if(a.find(k9) != &v9) printf("Dictionary: unit test 253 failing\n");
  if(b.find(s9) != &w9) printf("Dictionary: unit test 254 failing\n");
  // eighth delete
  a.del(k8);
  b.del(s8);
  if(!a.isCheckOk()) printf("Dictionary: unit test 255 failing\n");
  if(!b.isCheckOk()) printf("Dictionary: unit test 256 failing\n");
  // search should fail
  if(a.find(k8) != nullptr) printf("Dictionary: unit test 257 failing\n");
  if(b.find(s8) != nullptr) printf("Dictionary: unit test 258 failing\n");
  // search should succeed
  if(a.find(k9) != &v9) printf("Dictionary: unit test 259 failing\n");
  if(b.find(s9) != &w9) printf("Dictionary: unit test 260 failing\n");
  // ninth delete
  a.del(k9);
  b.del(s9);
  if(!a.isCheckOk()) printf("Dictionary: unit test 261 failing\n");
  if(!b.isCheckOk()) printf("Dictionary: unit test 262 failing\n");
  // search should fail
  if(a.find(k9) != nullptr) printf("Dictionary: unit test 263 failing\n");
  if(b.find(s9) != nullptr) printf("Dictionary: unit test 264 failing\n");
  // multiple inserts
  #define MAX_NUM 1024
  int keys[MAX_NUM];
  int vals[MAX_NUM];
  for(int i = 0; i < MAX_NUM; ++i){
    keys[i] = -1;
    vals[i] = -1;
  }
  for(int i = 0; i < MAX_NUM; ++i){
    keys[i] = i;
    vals[i] = i*10;
    a.insert(keys[i],&vals[i]);
    for(int j = 0; j <= i; ++j){
      if(a.find(keys[j]) != &vals[j]){
        printf("Dictionary: unit test 265 failing\n");
      }
    }
    for(int j = i+1; j < MAX_NUM; ++j){
      if(a.find(keys[j]) != nullptr){
        printf("Dictionary: unit test 266 failing\n");
      }
    }
  }
  // multiple deletes
  for(int i = 0; i < MAX_NUM; ++i){
    a.del(keys[i]);
    for(int j = 0; j <= i; ++j){
      if(a.find(keys[j]) != nullptr){
        printf("Dictionary: unit test 267 failing\n");
      }
    }
    for(int j = i+1; j < MAX_NUM; ++j){
      if(a.find(keys[j]) != &vals[j]){
        printf("Dictionary: unit test 268 failing\n");
      }
    }
  }


//  a.debug(printInt,printInt);
//  b.debug(printStr,printInt);


  printf("Dictionary: unit test complete\n");

  return 0;

}
