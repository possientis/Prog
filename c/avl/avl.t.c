// avl.t.c
#ifndef INCLUDED_AVL
#include "avl.h"
#endif

#include <stdio.h>


static void printKey(const void* k)
{
  int key = *(int*) k;
  printf("%d",key);
}

static int comp1(const void* x, const void* y)
{
  int u = *(int*) x;
  int v = *(int*) y;

  return (u - v);

}

static int comp2(const void* x, const void* y)
{
  int u = *(int*) x;
  int v = *(int*) y;

  return (v - u);

}

int main(int argc, char * argv[]){


  const void* key;  // temporary

  int v4m,v2m,v0,v1,v2,v3,v4,v5,v6,v7,v8; // some values
  int k6m,k4m,k3m,k2m,k1m,k0,k1,k2,k3,k4,k5,k6,k7,k8,k10; // some keys

  k6m = -6;
  k4m = -4;
  k3m = -3;
  k2m = -2;
  k1m = -1;
  k0 = 0;
  k1 = 1;
  k2 = 2;
  k3 = 3;
  k4 = 4;
  k5 = 5;
  k6 = 6;
  k7 = 7;
  k8 = 8;
  k10 = 10;

  v4m = -40;
  v2m = -20;
  v0 = 0;
  v1 = 10;
  v2 = 20;
  v3 = 30;
  v4 = 40;
  v5 = 50;
  v6 = 60;
  v7 = 70;
  v8 = 80;

  AVL a(comp1);  // instantiating avl tree
  AVL b(comp2);  // instantiating avl tree

  printf("AVL: starting unit test\n");

  // Insert, Min, Max
  // first insert
  a.insert(&k2,&v2);
  b.insert(&k2,&v2);
  if(!a.check()) printf("AVL: unit test 1 failing\n");
  if(!b.check()) printf("AVL: unit test 2 failing\n");
  if(a.min(key) != &v2) printf("AVL: unit test 3 failing\n");
  if(key != &k2) printf("AVL: unit test 4 failing\n");
  if(a.max(key) != &v2) printf("AVL: unit test 5 failing\n");
  if(key != &k2) printf("AVL: unit test 6 failing\n");
  if(b.min(key) != &v2) printf("AVL: unit test 7 failing\n");
  if(key != &k2) printf("AVL: unit test 8 failing\n");
  if(b.max(key) != &v2) printf("AVL: unit test 9 failing\n");
  if(key != &k2) printf("AVL: unit test 10 failing\n");
  // second insert
  a.insert(&k6,&v6);
  b.insert(&k6,&v6);
  if(!a.check()) printf("AVL: unit test 11 failing\n");
  if(!b.check()) printf("AVL: unit test 12 failing\n");
  if(a.min(key) != &v2) printf("AVL: unit test 13 failing\n");
  if(key != &k2) printf("AVL: unit test 14 failing\n");
  if(a.max(key) != &v6) printf("AVL: unit test 15 failing\n");
  if(key != &k6) printf("AVL: unit test 16 failing\n");
  if(b.min(key) != &v6) printf("AVL: unit test 17 failing\n");
  if(key != &k6) printf("AVL: unit test 18 failing\n");
  if(b.max(key) != &v2) printf("AVL: unit test 19 failing\n");
  if(key != &k2) printf("AVL: unit test 20 failing\n");
  // third insert
  a.insert(&k4,&v4);
  b.insert(&k4,&v4);
  if(!a.check()) printf("AVL: unit test 21 failing\n");
  if(!b.check()) printf("AVL: unit test 22 failing\n");
  if(a.min(key) != &v2) printf("AVL: unit test 23 failing\n");
  if(key != &k2) printf("AVL: unit test 24 failing\n");
  if(a.max(key) != &v6) printf("AVL: unit test 25 failing\n");
  if(key != &k6) printf("AVL: unit test 26 failing\n");
  if(b.min(key) != &v6) printf("AVL: unit test 27 failing\n");
  if(key != &k6) printf("AVL: unit test 28 failing\n");
  if(b.max(key) != &v2) printf("AVL: unit test 29 failing\n");
  if(key != &k2) printf("AVL: unit test 30 failing\n");
  // fourth insert
  a.insert(&k2m,&v2m);
  b.insert(&k2m,&v2m);
  if(!a.check()) printf("AVL: unit test 31 failing\n");
  if(!b.check()) printf("AVL: unit test 32 failing\n");
  if(a.min(key) != &v2m) printf("AVL: unit test 33 failing\n");
  if(key != &k2m) printf("AVL: unit test 34 failing\n");
  if(a.max(key) != &v6) printf("AVL: unit test 35 failing\n");
  if(key != &k6) printf("AVL: unit test 36 failing\n");
  if(b.min(key) != &v6) printf("AVL: unit test 37 failing\n");
  if(key != &k6) printf("AVL: unit test 38 failing\n");
  if(b.max(key) != &v2m) printf("AVL: unit test 39 failing\n");
  if(key != &k2m) printf("AVL: unit test 40 failing\n");
  // further inserts
  a.insert(&k4m,&v4m);
  b.insert(&k4m,&v4m);
  if(!a.check()) printf("AVL: unit test 40.1 failing\n");
  if(!b.check()) printf("AVL: unit test 40.2 failing\n");
  a.insert(&k0,&v0);
  b.insert(&k0,&v0);
  if(!a.check()) printf("AVL: unit test 40.3 failing\n");
  if(!b.check()) printf("AVL: unit test 40.4 failing\n");
  a.insert(&k8,&v8);
  b.insert(&k8,&v8);
  if(!a.check()) printf("AVL: unit test 41 failing\n");
  if(!b.check()) printf("AVL: unit test 42 failing\n");
  if(a.min(key) != &v4m) printf("AVL: unit test 43 failing\n");
  if(key != &k4m) printf("AVL: unit test 44 failing\n");
  if(a.max(key) != &v8) printf("AVL: unit test 45 failing\n");
  if(key != &k8) printf("AVL: unit test 46 failing\n");
  if(b.min(key) != &v8) printf("AVL: unit test 47 failing\n");
  if(key != &k8) printf("AVL: unit test 48 failing\n");
  if(b.max(key) != &v4m) printf("AVL: unit test 49 failing\n");
  if(key != &k4m) printf("AVL: unit test 50 failing\n");
  // testing find
  // key 1
  if(a.find(&k4) != &v4) printf("AVL: unit test 52 failing\n");
  if(b.find(&k4) != &v4) printf("AVL: unit test 54 failing\n");
  // key -1
  if(a.find(&k2m) != &v2m) printf("AVL: unit test 56 failing\n");
  if(b.find(&k2m) != &v2m) printf("AVL: unit test 58 failing\n");
  // key -2
  if(a.find(&k4m) != &v4m) printf("AVL: unit test 60 failing\n");
  if(b.find(&k4m) != &v4m) printf("AVL: unit test 62 failing\n");
  // key 0
  if(a.find(&k0) != &v0) printf("AVL: unit test 64 failing\n");
  if(b.find(&k0) != &v0) printf("AVL: unit test 66 failing\n");
  // key 3
  if(a.find(&k6) != &v6) printf("AVL: unit test 68 failing\n");
  if(b.find(&k6) != &v6) printf("AVL: unit test 70 failing\n");
  // key 2
  if(a.find(&k4) != &v4) printf("AVL: unit test 72 failing\n");
  if(b.find(&k4) != &v4) printf("AVL: unit test 74 failing\n");
  // key 4
  if(a.find(&k8) != &v8) printf("AVL: unit test 76 failing\n");
  if(b.find(&k8) != &v8) printf("AVL: unit test 78 failing\n");
  // key 5
  if(a.find(&k10) != nullptr) printf("AVL: unit test 79 failing\n");
  if(b.find(&k10) != nullptr) printf("AVL: unit test 80 failing\n");
  // testing no side effect
  if(!a.check()) printf("AVL: unit test 81 failing\n");
  if(!b.check()) printf("AVL: unit test 82 failing\n");
  // testing succ
  // -6
  if(a.succ(&k6m,key) != &v4m) printf("AVL: unit test 83 failing\n");
  if(key != &k4m) printf("AVL: unit test 84 failing\n");
  if(b.succ(&k6m,key) != nullptr) printf("AVL: unit test 85 failing\n");
  // -4
  if(a.succ(&k4m,key) != &v2m) printf("AVL: unit test 86 failing\n");
  if(key != &k2m) printf("AVL: unit test 87 failing\n");
  if(b.succ(&k4m,key) != nullptr) printf("AVL: unit test 88 failing\n");
  // -3
  if(a.succ(&k3m,key) != &v2m) printf("AVL: unit test 89 failing\n");
  if(key != &k2m) printf("AVL: unit test 90 failing\n");
  if(b.succ(&k3m,key) != &v4m) printf("AVL: unit test 91 failing\n");
  if(key != &k4m) printf("AVL: unit test 92 failing\n");
  // -2
  if(a.succ(&k2m,key) != &v0) printf("AVL: unit test 93 failing\n");
  if(key != &k0) printf("AVL: unit test 94 failing\n");
  if(b.succ(&k2m,key) != &v4m) printf("AVL: unit test 95 failing\n");
  if(key != &k4m) printf("AVL: unit test 96 failing\n");
  // -1
  if(a.succ(&k1m,key) != &v0) printf("AVL: unit test 97 failing\n");
  if(key != &k0) printf("AVL: unit test 98 failing\n");
  if(b.succ(&k1m,key) != &v2m) printf("AVL: unit test 99 failing\n");
  if(key != &k2m) printf("AVL: unit test 100 failing\n");
  // 0
  if(a.succ(&k0,key) != &v2) printf("AVL: unit test 101 failing\n");
  if(key != &k2) printf("AVL: unit test 102 failing\n");
  if(b.succ(&k0,key) != &v2m) printf("AVL: unit test 103 failing\n");
  if(key != &k2m) printf("AVL: unit test 104 failing\n");
  // 1
  if(a.succ(&k1,key) != &v2) printf("AVL: unit test 105 failing\n");
  if(key != &k2) printf("AVL: unit test 106 failing\n");
  if(b.succ(&k1,key) != &v0) printf("AVL: unit test 107 failing\n");
  if(key != &k0) printf("AVL: unit test 108 failing\n");
  // 2
  if(a.succ(&k2,key) != &v4) printf("AVL: unit test 109 failing\n");
  if(key != &k4) printf("AVL: unit test 110 failing\n");
  if(b.succ(&k2,key) != &v0) printf("AVL: unit test 111 failing\n");
  if(key != &k0) printf("AVL: unit test 112 failing\n");
  // 3
  if(a.succ(&k3,key) != &v4) printf("AVL: unit test 113 failing\n");
  if(key != &k4) printf("AVL: unit test 114 failing\n");
  if(b.succ(&k3,key) != &v2) printf("AVL: unit test 115 failing\n");
  if(key != &k2) printf("AVL: unit test 116 failing\n");
  // 4
  if(a.succ(&k4,key) != &v6) printf("AVL: unit test 117 failing\n");
  if(key != &k6) printf("AVL: unit test 118 failing\n");
  if(b.succ(&k4,key) != &v2) printf("AVL: unit test 119 failing\n");
  if(key != &k2) printf("AVL: unit test 120 failing\n");
  // 5
  if(a.succ(&k5,key) != &v6) printf("AVL: unit test 121 failing\n");
  if(key != &k6) printf("AVL: unit test 122 failing\n");
  if(b.succ(&k5,key) != &v4) printf("AVL: unit test 123 failing\n");
  if(key != &k4) printf("AVL: unit test 124 failing\n");
  // 6
  if(a.succ(&k6,key) != &v8) printf("AVL: unit test 125 failing\n");
  if(key != &k8) printf("AVL: unit test 126 failing\n");
  if(b.succ(&k6,key) != &v4) printf("AVL: unit test 127 failing\n");
  if(key != &k4) printf("AVL: unit test 128 failing\n");
  // 7
  if(a.succ(&k7,key) != &v8) printf("AVL: unit test 129 failing\n");
  if(key != &k8) printf("AVL: unit test 130 failing\n");
  if(b.succ(&k7,key) != &v6) printf("AVL: unit test 131 failing\n");
  if(key != &k6) printf("AVL: unit test 132 failing\n");
  // 8
  if(a.succ(&k8,key) != nullptr) printf("AVL: unit test 133 failing\n");
  if(b.succ(&k8,key) != &v6) printf("AVL: unit test 134 failing\n");
  if(key != &k6) printf("AVL: unit test 135 failing\n");
  // 10
  if(a.succ(&k10,key) != nullptr) printf("AVL: unit test 136 failing\n");
  if(b.succ(&k10,key) != &v8) printf("AVL: unit test 137 failing\n");
  if(key != &k8) printf("AVL: unit test 138 failing\n");
  // testing pred
  // -6
  if(b.pred(&k6m,key) != &v4m) printf("AVL: unit test 139 failing\n");
  if(key != &k4m) printf("AVL: unit test 140 failing\n");
  if(a.pred(&k6m,key) != nullptr) printf("AVL: unit test 141 failing\n");
  // -4
  if(b.pred(&k4m,key) != &v2m) printf("AVL: unit test 142 failing\n");
  if(key != &k2m) printf("AVL: unit test 143 failing\n");
  if(a.pred(&k4m,key) != nullptr) printf("AVL: unit test 144 failing\n");
  // -3
  if(b.pred(&k3m,key) != &v2m) printf("AVL: unit test 145 failing\n");
  if(key != &k2m) printf("AVL: unit test 146 failing\n");
  if(a.pred(&k3m,key) != &v4m) printf("AVL: unit test 147 failing\n");
  if(key != &k4m) printf("AVL: unit test 148 failing\n");
  // -2
  if(b.pred(&k2m,key) != &v0) printf("AVL: unit test 149 failing\n");
  if(key != &k0) printf("AVL: unit test 150 failing\n");
  if(a.pred(&k2m,key) != &v4m) printf("AVL: unit test 151 failing\n");
  if(key != &k4m) printf("AVL: unit test 152 failing\n");
  // -1
  if(b.pred(&k1m,key) != &v0) printf("AVL: unit test 153 failing\n");
  if(key != &k0) printf("AVL: unit test 154 failing\n");
  if(a.pred(&k1m,key) != &v2m) printf("AVL: unit test 155 failing\n");
  if(key != &k2m) printf("AVL: unit test 156 failing\n");
  // 0
  if(b.pred(&k0,key) != &v2) printf("AVL: unit test 157 failing\n");
  if(key != &k2) printf("AVL: unit test 158 failing\n");
  if(a.pred(&k0,key) != &v2m) printf("AVL: unit test 159 failing\n");
  if(key != &k2m) printf("AVL: unit test 160 failing\n");
  // 1
  if(b.pred(&k1,key) != &v2) printf("AVL: unit test 161 failing\n");
  if(key != &k2) printf("AVL: unit test 162 failing\n");
  if(a.pred(&k1,key) != &v0) printf("AVL: unit test 163 failing\n");
  if(key != &k0) printf("AVL: unit test 164 failing\n");
  // 2
  if(b.pred(&k2,key) != &v4) printf("AVL: unit test 165 failing\n");
  if(key != &k4) printf("AVL: unit test 166 failing\n");
  if(a.pred(&k2,key) != &v0) printf("AVL: unit test 167 failing\n");
  if(key != &k0) printf("AVL: unit test 168 failing\n");
  // 3
  if(b.pred(&k3,key) != &v4) printf("AVL: unit test 169 failing\n");
  if(key != &k4) printf("AVL: unit test 170 failing\n");
  if(a.pred(&k3,key) != &v2) printf("AVL: unit test 171 failing\n");
  if(key != &k2) printf("AVL: unit test 172 failing\n");
  // 4
  if(b.pred(&k4,key) != &v6) printf("AVL: unit test 173 failing\n");
  if(key != &k6) printf("AVL: unit test 174 failing\n");
  if(a.pred(&k4,key) != &v2) printf("AVL: unit test 175 failing\n");
  if(key != &k2) printf("AVL: unit test 176 failing\n");
  // 5
  if(b.pred(&k5,key) != &v6) printf("AVL: unit test 177 failing\n");
  if(key != &k6) printf("AVL: unit test 178 failing\n");
  if(a.pred(&k5,key) != &v4) printf("AVL: unit test 179 failing\n");
  if(key != &k4) printf("AVL: unit test 180 failing\n");
  // 6
  if(b.pred(&k6,key) != &v8) printf("AVL: unit test 181 failing\n");
  if(key != &k8) printf("AVL: unit test 182 failing\n");
  if(a.pred(&k6,key) != &v4) printf("AVL: unit test 183 failing\n");
  if(key != &k4) printf("AVL: unit test 184 failing\n");
  // 7
  if(b.pred(&k7,key) != &v8) printf("AVL: unit test 185 failing\n");
  if(key != &k8) printf("AVL: unit test 186 failing\n");
  if(a.pred(&k7,key) != &v6) printf("AVL: unit test 187 failing\n");
  if(key != &k6) printf("AVL: unit test 188 failing\n");
  // 8
  if(b.pred(&k8,key) != nullptr) printf("AVL: unit test 189 failing\n");
  if(a.pred(&k8,key) != &v6) printf("AVL: unit test 190 failing\n");
  if(key != &k6) printf("AVL: unit test 191 failing\n");
  // 10
  if(b.pred(&k10,key) != nullptr) printf("AVL: unit test 192 failing\n");
  if(a.pred(&k10,key) != &v8) printf("AVL: unit test 193 failing\n");
  if(key != &k8) printf("AVL: unit test 194 failing\n");
 // delete
  a.del(&k10);  // should have no impact
  b.del(&k10);  // should have no impact
  if(!a.check()) printf("AVL: unit test 195 failing\n");
  if(!b.check()) printf("AVL: unit test 196 failing\n");
  // delete 0
  a.del(&k0);
  b.del(&k0);
  if(!a.check()) printf("AVL: unit test 197 failing\n");
  if(!b.check()) printf("AVL: unit test 198 failing\n");
  if(a.find(&k0) != nullptr) printf("AVL: unit test 199 failing\n");
  if(b.find(&k0) != nullptr) printf("AVL: unit test 199 failing\n");
  if(a.find(&k4m) != &v4m) printf("AVL: unit test 200 failing\n");
  if(b.find(&k4m) != &v4m) printf("AVL: unit test 201 failing\n");
  if(a.find(&k2m) != &v2m) printf("AVL: unit test 202 failing\n");
  if(b.find(&k2m) != &v2m) printf("AVL: unit test 203 failing\n");
  if(a.find(&k2) != &v2) printf("AVL: unit test 204 failing\n");
  if(b.find(&k2) != &v2) printf("AVL: unit test 205 failing\n");
  if(a.find(&k4) != &v4) printf("AVL: unit test 206 failing\n");
  if(b.find(&k4) != &v4) printf("AVL: unit test 207 failing\n");
  if(a.find(&k6) != &v6) printf("AVL: unit test 208 failing\n");
  if(b.find(&k6) != &v6) printf("AVL: unit test 209 failing\n");
  if(a.find(&k8) != &v8) printf("AVL: unit test 210 failing\n");
  if(b.find(&k8) != &v8) printf("AVL: unit test 211 failing\n");
  // delete 8
  a.del(&k8);
  b.del(&k8);
  if(!a.check()) printf("AVL: unit test 212 failing\n");
  if(!b.check()) printf("AVL: unit test 213 failing\n");
  if(a.find(&k8) != nullptr) printf("AVL: unit test 214 failing\n");
  if(b.find(&k8) != nullptr) printf("AVL: unit test 215 failing\n");
  if(a.find(&k4m) != &v4m) printf("AVL: unit test 216 failing\n");
  if(b.find(&k4m) != &v4m) printf("AVL: unit test 217 failing\n");
  if(a.find(&k2m) != &v2m) printf("AVL: unit test 218 failing\n");
  if(b.find(&k2m) != &v2m) printf("AVL: unit test 219 failing\n");
  if(a.find(&k2) != &v2) printf("AVL: unit test 220 failing\n");
  if(b.find(&k2) != &v2) printf("AVL: unit test 221 failing\n");
  if(a.find(&k4) != &v4) printf("AVL: unit test 222 failing\n");
  if(b.find(&k4) != &v4) printf("AVL: unit test 223 failing\n");
  if(a.find(&k6) != &v6) printf("AVL: unit test 224 failing\n");
  if(b.find(&k6) != &v6) printf("AVL: unit test 225 failing\n");
  // delete -4
  a.del(&k4m);
  b.del(&k4m);
  if(!a.check()) printf("AVL: unit test 226 failing\n");
  if(!b.check()) printf("AVL: unit test 227 failing\n");
  if(a.find(&k4m) != nullptr) printf("AVL: unit test 228 failing\n");
  if(b.find(&k4m) != nullptr) printf("AVL: unit test 229 failing\n");
  if(a.find(&k2m) != &v2m) printf("AVL: unit test 230 failing\n");
  if(b.find(&k2m) != &v2m) printf("AVL: unit test 231 failing\n");
  if(a.find(&k2) != &v2) printf("AVL: unit test 232 failing\n");
  if(b.find(&k2) != &v2) printf("AVL: unit test 233 failing\n");
  if(a.find(&k4) != &v4) printf("AVL: unit test 234 failing\n");
  if(b.find(&k4) != &v4) printf("AVL: unit test 235 failing\n");
  if(a.find(&k6) != &v6) printf("AVL: unit test 236 failing\n");
  if(b.find(&k6) != &v6) printf("AVL: unit test 237 failing\n");
  // delete 4
  a.del(&k4);
  b.del(&k4);
  if(!a.check()) printf("AVL: unit test 238 failing\n");
  if(!b.check()) printf("AVL: unit test 239 failing\n");
  if(a.find(&k4m) != nullptr) printf("AVL: unit test 240 failing\n");
  if(b.find(&k4m) != nullptr) printf("AVL: unit test 241 failing\n");
  if(a.find(&k2m) != &v2m) printf("AVL: unit test 242 failing\n");
  if(b.find(&k2m) != &v2m) printf("AVL: unit test 243 failing\n");
  if(a.find(&k2) != &v2) printf("AVL: unit test 244 failing\n");
  if(b.find(&k2) != &v2) printf("AVL: unit test 245 failing\n");
  if(a.find(&k6) != &v6) printf("AVL: unit test 246 failing\n");
  if(b.find(&k6) != &v6) printf("AVL: unit test 247 failing\n");
  // delete 2
  a.del(&k2);
  b.del(&k2);
  if(!a.check()) printf("AVL: unit test 248 failing\n");
  if(!b.check()) printf("AVL: unit test 249 failing\n");
  if(a.find(&k2) != nullptr) printf("AVL: unit test 250 failing\n");
  if(b.find(&k2) != nullptr) printf("AVL: unit test 251 failing\n");
  if(a.find(&k2m) != &v2m) printf("AVL: unit test 252 failing\n");
  if(b.find(&k2m) != &v2m) printf("AVL: unit test 253 failing\n");
  if(a.find(&k6) != &v6) printf("AVL: unit test 254 failing\n");
  if(b.find(&k6) != &v6) printf("AVL: unit test 255 failing\n");
  // delete -2
  a.del(&k2m);
  b.del(&k2m);
  if(!a.check()) printf("AVL: unit test 256 failing\n");
  if(!b.check()) printf("AVL: unit test 257 failing\n");
  if(a.find(&k2m) != nullptr) printf("AVL: unit test 258 failing\n");
  if(b.find(&k2m) != nullptr) printf("AVL: unit test 259 failing\n");
  if(a.find(&k6) != &v6) printf("AVL: unit test 260 failing\n");
  if(b.find(&k6) != &v6) printf("AVL: unit test 261 failing\n");
  // delete 6
  a.del(&k6);
  b.del(&k6);
  if(!a.check()) printf("AVL: unit test 262 failing\n");
  if(!b.check()) printf("AVL: unit test 263 failing\n");
  if(a.find(&k6) != nullptr) printf("AVL: unit test 264 failing\n");
  if(b.find(&k6) != nullptr) printf("AVL: unit test 265 failing\n");
  // checking avl property more thoroughly
  a.insert(&k1,&v1);
  b.insert(&k1,&v1);
  if(!a.check()) printf("AVL: unit test 266 failing\n");
  if(!b.check()) printf("AVL: unit test 267 failing\n");
  a.insert(&k2,&v2);
  b.insert(&k2,&v2);
  if(!a.check()) printf("AVL: unit test 268 failing\n");
  if(!b.check()) printf("AVL: unit test 269 failing\n");
  a.insert(&k3,&v3);
  b.insert(&k3,&v3);
  if(!a.check()) printf("AVL: unit test 270 failing\n");
  if(!b.check()) printf("AVL: unit test 271 failing\n");
  a.insert(&k4,&v4);
  b.insert(&k4,&v4);
  if(!a.check()) printf("AVL: unit test 272 failing\n");
  if(!b.check()) printf("AVL: unit test 273 failing\n");
  a.insert(&k5,&v5);
  b.insert(&k5,&v5);
  if(!a.check()) printf("AVL: unit test 274 failing\n");
  if(!b.check()) printf("AVL: unit test 275 failing\n");
  a.insert(&k6,&v6);
  b.insert(&k6,&v6);
  if(!a.check()) printf("AVL: unit test 276 failing\n");
  if(!b.check()) printf("AVL: unit test 277 failing\n");
  a.insert(&k7,&v7);
  b.insert(&k7,&v7);
  if(!a.check()) printf("AVL: unit test 278 failing\n");
  if(!b.check()) printf("AVL: unit test 279 failing\n");
  a.insert(&k8,&v8);
  b.insert(&k8,&v8);
  if(!a.check()) printf("AVL: unit test 280 failing\n");
  if(!b.check()) printf("AVL: unit test 281 failing\n");
  a.del(&k5);
  b.del(&k5);
  if(!a.check()) printf("AVL: unit test 282 failing\n");
  if(!b.check()) printf("AVL: unit test 283 failing\n");
  a.del(&k4);
  b.del(&k4);
  if(!a.check()) printf("AVL: unit test 284 failing\n");
  if(!b.check()) printf("AVL: unit test 285 failing\n");
  a.del(&k7);
  b.del(&k7);
  if(!a.check()) printf("AVL: unit test 286 failing\n");
  if(!b.check()) printf("AVL: unit test 287 failing\n");
  a.insert(&k0,&v0);
  b.insert(&k0,&v0);
  if(!a.check()) printf("AVL: unit test 288 failing\n");
  if(!b.check()) printf("AVL: unit test 289 failing\n");
  a.del(&k6);
  b.del(&k6);
  if(!a.check()) printf("AVL: unit test 290 failing\n");
  if(!b.check()) printf("AVL: unit test 291 failing\n");
  a.del(&k3);
  b.del(&k3);
  if(!a.check()) printf("AVL: unit test 292 failing\n");
  if(!b.check()) printf("AVL: unit test 293 failing\n");
  a.del(&k8);
  b.del(&k8);
  if(!a.check()) printf("AVL: unit test 294 failing\n");
  if(!b.check()) printf("AVL: unit test 295 failing\n");
  a.del(&k0);
  b.del(&k0);
  if(!a.check()) printf("AVL: unit test 296 failing\n");
  if(!b.check()) printf("AVL: unit test 296 failing\n");
  a.del(&k1);
  b.del(&k1);
  if(!a.check()) printf("AVL: unit test 297 failing\n");
  if(!b.check()) printf("AVL: unit test 298 failing\n");
  a.del(&k2);
  b.del(&k2);
  if(!a.check()) printf("AVL: unit test 299 failing\n");
  if(!b.check()) printf("AVL: unit test 300 failing\n");
  a.del(&k1);
  b.del(&k1);
  if(!a.check()) printf("AVL: unit test 301 failing\n");
  if(!b.check()) printf("AVL: unit test 302 failing\n");

  int const N = 511;
  int k[N];
  for(int i = 0; i < N; i++){

    k[i] = i;
    a.insert(&k[i],&v0);
    b.insert(&k[i],&v0);
    if(!a.check()) printf("AVL: unit test 303 failing\n");
    if(!b.check()) printf("AVL: unit test 304 failing\n");

  }

  for(int i = 0; i < N; i++){

    a.del(&k[i]);
    b.del(&k[i]);
    if(!a.check()) printf("AVL: unit test 305 failing\n");
    if(!b.check()) printf("AVL: unit test 306 failing\n");

  }


//  printf("\nFinal tree:\n");
//  a.print(printKey);
//  printf("\n\n");

  printf("AVL: unit test complete\n");

  return 0;

}
