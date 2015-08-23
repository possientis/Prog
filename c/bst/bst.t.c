// bst.t.c
#ifndef INCLUDED_BST
#include "bst.h"
#endif

#include <stdio.h>


struct T{ // some user defined type for tree node values
  int value;
};


int comp1(int x, int y){return (x - y);} // comparison operator
int comp2(int x, int y){return (y - x);} // comparison operator

int main(int argc, char * argv[]){


  int key;  // temporary

  T v4m,v2m,v0,v2,v4,v6,v8; // some values

  v4m.value = -40;
  v2m.value = -20;
  v0.value = 0;
  v2.value = 20;
  v4.value = 40;
  v6.value = 60;
  v8.value = 80;

  BST<int,T> a(comp1);  // instantiating binary find tree
  BST<int,T> b(comp2);  // instantiating binary find tree

  printf("BST: starting unit test\n");

  // Insert, Min, Max
  // first insert
  a.insert(2,&v2);
  b.insert(2,&v2);
  if(!a.check()) printf("BST: unit test 1 failing\n");
  if(!b.check()) printf("BST: unit test 2 failing\n");
  if(a.min(key) != &v2) printf("BST: unit test 3 failing\n");
  if(key != 2) printf("BST: unit test 4 failing\n");
  if(a.max(key) != &v2) printf("BST: unit test 5 failing\n");
  if(key != 2) printf("BST: unit test 6 failing\n");
  if(b.min(key) != &v2) printf("BST: unit test 7 failing\n");
  if(key != 2) printf("BST: unit test 8 failing\n");
  if(b.max(key) != &v2) printf("BST: unit test 9 failing\n");
  if(key != 2) printf("BST: unit test 10 failing\n");
  // second insert
  a.insert(6,&v6);
  b.insert(6,&v6);
  if(!a.check()) printf("BST: unit test 11 failing\n");
  if(!b.check()) printf("BST: unit test 12 failing\n");
  if(a.min(key) != &v2) printf("BST: unit test 13 failing\n");
  if(key != 2) printf("BST: unit test 14 failing\n");
  if(a.max(key) != &v6) printf("BST: unit test 15 failing\n");
  if(key != 6) printf("BST: unit test 16 failing\n");
  if(b.min(key) != &v6) printf("BST: unit test 17 failing\n");
  if(key != 6) printf("BST: unit test 18 failing\n");
  if(b.max(key) != &v2) printf("BST: unit test 19 failing\n");
  if(key != 2) printf("BST: unit test 20 failing\n");
  // third insert
  a.insert(4,&v4);
  b.insert(4,&v4);
  if(!a.check()) printf("BST: unit test 21 failing\n");
  if(!b.check()) printf("BST: unit test 22 failing\n");
  if(a.min(key) != &v2) printf("BST: unit test 23 failing\n");
  if(key != 2) printf("BST: unit test 24 failing\n");
  if(a.max(key) != &v6) printf("BST: unit test 25 failing\n");
  if(key != 6) printf("BST: unit test 26 failing\n");
  if(b.min(key) != &v6) printf("BST: unit test 27 failing\n");
  if(key != 6) printf("BST: unit test 28 failing\n");
  if(b.max(key) != &v2) printf("BST: unit test 29 failing\n");
  if(key != 2) printf("BST: unit test 30 failing\n");
  // fourth insert
  a.insert(-2,&v2m);
  b.insert(-2,&v2m);
  if(!a.check()) printf("BST: unit test 31 failing\n");
  if(!b.check()) printf("BST: unit test 32 failing\n");
  if(a.min(key) != &v2m) printf("BST: unit test 33 failing\n");
  if(key != -2) printf("BST: unit test 34 failing\n");
  if(a.max(key) != &v6) printf("BST: unit test 35 failing\n");
  if(key != 6) printf("BST: unit test 36 failing\n");
  if(b.min(key) != &v6) printf("BST: unit test 37 failing\n");
  if(key != 6) printf("BST: unit test 38 failing\n");
  if(b.max(key) != &v2m) printf("BST: unit test 39 failing\n");
  if(key != -2) printf("BST: unit test 40 failing\n");
  // further inserts
  a.insert(-4,&v4m);
  b.insert(-4,&v4m);
  a.insert(0,&v0);
  b.insert(0,&v0);
  a.insert(8,&v8);
  b.insert(8,&v8);
  if(!a.check()) printf("BST: unit test 41 failing\n");
  if(!b.check()) printf("BST: unit test 42 failing\n");
  if(a.min(key) != &v4m) printf("BST: unit test 43 failing\n");
  if(key != -4) printf("BST: unit test 44 failing\n");
  if(a.max(key) != &v8) printf("BST: unit test 45 failing\n");
  if(key != 8) printf("BST: unit test 46 failing\n");
  if(b.min(key) != &v8) printf("BST: unit test 47 failing\n");
  if(key != 8) printf("BST: unit test 48 failing\n");
  if(b.max(key) != &v4m) printf("BST: unit test 49 failing\n");
  if(key != -4) printf("BST: unit test 50 failing\n");
  // testing find
  // key 1
  if(a.find(4) != &v4) printf("BST: unit test 52 failing\n");
  if(b.find(4) != &v4) printf("BST: unit test 54 failing\n");
  // key -1
  if(a.find(-2) != &v2m) printf("BST: unit test 56 failing\n");
  if(b.find(-2) != &v2m) printf("BST: unit test 58 failing\n");
  // key -2
  if(a.find(-4) != &v4m) printf("BST: unit test 60 failing\n");
  if(b.find(-4) != &v4m) printf("BST: unit test 62 failing\n");
  // key 0
  if(a.find(0) != &v0) printf("BST: unit test 64 failing\n");
  if(b.find(0) != &v0) printf("BST: unit test 66 failing\n");
  // key 3
  if(a.find(6) != &v6) printf("BST: unit test 68 failing\n");
  if(b.find(6) != &v6) printf("BST: unit test 70 failing\n");
  // key 2
  if(a.find(4) != &v4) printf("BST: unit test 72 failing\n");
  if(b.find(4) != &v4) printf("BST: unit test 74 failing\n");
  // key 4
  if(a.find(8) != &v8) printf("BST: unit test 76 failing\n");
  if(b.find(8) != &v8) printf("BST: unit test 78 failing\n");
  // key 5
  if(a.find(10) != nullptr) printf("BST: unit test 79 failing\n");
  if(b.find(10) != nullptr) printf("BST: unit test 80 failing\n");
  // testing no side effect
  if(!a.check()) printf("BST: unit test 81 failing\n");
  if(!b.check()) printf("BST: unit test 82 failing\n");
  // testing succ
  // -6
  if(a.succ(-6,&key) != &v4m) printf("BST: unit test 83 failing\n");
  if(key != -4) printf("BST: unit test 84 failing\n");
  if(b.succ(-6,&key) != nullptr) printf("BST: unit test 85 failing\n");
  // -4
  if(a.succ(-4,&key) != &v2m) printf("BST: unit test 86 failing\n");
  if(key != -2) printf("BST: unit test 87 failing\n");
  if(b.succ(-4,&key) != nullptr) printf("BST: unit test 88 failing\n");
  // -3
  if(a.succ(-3,&key) != &v2m) printf("BST: unit test 89 failing\n");
  if(key != -2) printf("BST: unit test 90 failing\n");
  if(b.succ(-3,&key) != &v4m) printf("BST: unit test 91 failing\n");
  if(key != -4) printf("BST: unit test 92 failing\n");
  // -2
  if(a.succ(-2,&key)->value != 0) printf("BST: unit test 93 failing\n");
  if(key != 0) printf("BST: unit test 94 failing\n");
  if(b.succ(-2,&key) != &v4m) printf("BST: unit test 95 failing\n");
  if(key != -4) printf("BST: unit test 96 failing\n");
  // -1
  if(a.succ(-1,&key) != &v0) printf("BST: unit test 97 failing\n");
  if(key != 0) printf("BST: unit test 98 failing\n");
  if(b.succ(-1,&key) != &v2m) printf("BST: unit test 99 failing\n");
  if(key != -2) printf("BST: unit test 100 failing\n");
  // 0
  if(a.succ(0,&key) != &v2) printf("BST: unit test 101 failing\n");
  if(key != 2) printf("BST: unit test 102 failing\n");
  if(b.succ(0,&key) != &v2m) printf("BST: unit test 103 failing\n");
  if(key != -2) printf("BST: unit test 104 failing\n");
  // 1
  if(a.succ(1,&key) != &v2) printf("BST: unit test 105 failing\n");
  if(key != 2) printf("BST: unit test 106 failing\n");
  if(b.succ(1,&key) != &v0) printf("BST: unit test 107 failing\n");
  if(key != 0) printf("BST: unit test 108 failing\n");
  // 2
  if(a.succ(2,&key) != &v4) printf("BST: unit test 109 failing\n");
  if(key != 4) printf("BST: unit test 110 failing\n");
  if(b.succ(2,&key) != &v0) printf("BST: unit test 111 failing\n");
  if(key != 0) printf("BST: unit test 112 failing\n");
  // 3
  if(a.succ(3,&key) != &v4) printf("BST: unit test 113 failing\n");
  if(key != 4) printf("BST: unit test 114 failing\n");
  if(b.succ(3,&key) != &v2) printf("BST: unit test 115 failing\n");
  if(key != 2) printf("BST: unit test 116 failing\n");
  // 4
  if(a.succ(4,&key) != &v6) printf("BST: unit test 117 failing\n");
  if(key != 6) printf("BST: unit test 118 failing\n");
  if(b.succ(4,&key) != &v2) printf("BST: unit test 119 failing\n");
  if(key != 2) printf("BST: unit test 120 failing\n");
  // 5
  if(a.succ(5,&key) != &v6) printf("BST: unit test 121 failing\n");
  if(key != 6) printf("BST: unit test 122 failing\n");
  if(b.succ(5,&key) != &v4) printf("BST: unit test 123 failing\n");
  if(key != 4) printf("BST: unit test 124 failing\n");
  // 6
  if(a.succ(6,&key) != &v8) printf("BST: unit test 125 failing\n");
  if(key != 8) printf("BST: unit test 126 failing\n");
  if(b.succ(6,&key) != &v4) printf("BST: unit test 127 failing\n");
  if(key != 4) printf("BST: unit test 128 failing\n");
  // 7
  if(a.succ(7,&key) != &v8) printf("BST: unit test 129 failing\n");
  if(key != 8) printf("BST: unit test 130 failing\n");
  if(b.succ(7,&key) != &v6) printf("BST: unit test 131 failing\n");
  if(key != 6) printf("BST: unit test 132 failing\n");
  // 8
  if(a.succ(8,&key) != nullptr) printf("BST: unit test 133 failing\n");
  if(b.succ(8,&key) != &v6) printf("BST: unit test 134 failing\n");
  if(key != 6) printf("BST: unit test 135 failing\n");
  // 10
  if(a.succ(10,&key) != nullptr) printf("BST: unit test 136 failing\n");
  if(b.succ(10,&key) != &v8) printf("BST: unit test 137 failing\n");
  if(key != 8) printf("BST: unit test 138 failing\n");
  // testing pred
  // -6
  if(b.pred(-6,&key) != &v4m) printf("BST: unit test 139 failing\n");
  if(key != -4) printf("BST: unit test 140 failing\n");
  if(a.pred(-6,&key) != nullptr) printf("BST: unit test 141 failing\n");
  // -4
  if(b.pred(-4,&key)->value != -20) printf("BST: unit test 142 failing\n");
  if(key != -2) printf("BST: unit test 143 failing\n");
  if(a.pred(-4,&key) != nullptr) printf("BST: unit test 144 failing\n");
  // -3
  if(b.pred(-3,&key) != &v2m) printf("BST: unit test 145 failing\n");
  if(key != -2) printf("BST: unit test 146 failing\n");
  if(a.pred(-3,&key) != &v4m) printf("BST: unit test 147 failing\n");
  if(key != -4) printf("BST: unit test 148 failing\n");
  // -2
  if(b.pred(-2,&key) != &v0) printf("BST: unit test 149 failing\n");
  if(key != 0) printf("BST: unit test 150 failing\n");
  if(a.pred(-2,&key) != &v4m) printf("BST: unit test 151 failing\n");
  if(key != -4) printf("BST: unit test 152 failing\n");
  // -1
  if(b.pred(-1,&key) != &v0) printf("BST: unit test 153 failing\n");
  if(key != 0) printf("BST: unit test 154 failing\n");
  if(a.pred(-1,&key) != &v2m) printf("BST: unit test 155 failing\n");
  if(key != -2) printf("BST: unit test 156 failing\n");
  // 0
  if(b.pred(0,&key) != &v2) printf("BST: unit test 157 failing\n");
  if(key != 2) printf("BST: unit test 158 failing\n");
  if(a.pred(0,&key) != &v2m) printf("BST: unit test 159 failing\n");
  if(key != -2) printf("BST: unit test 160 failing\n");
  // 1
  if(b.pred(1,&key) != &v2) printf("BST: unit test 161 failing\n");
  if(key != 2) printf("BST: unit test 162 failing\n");
  if(a.pred(1,&key) != &v0) printf("BST: unit test 163 failing\n");
  if(key != 0) printf("BST: unit test 164 failing\n");
  // 2
  if(b.pred(2,&key) != &v4) printf("BST: unit test 165 failing\n");
  if(key != 4) printf("BST: unit test 166 failing\n");
  if(a.pred(2,&key) != &v0) printf("BST: unit test 167 failing\n");
  if(key != 0) printf("BST: unit test 168 failing\n");
  // 3
  if(b.pred(3,&key) != &v4) printf("BST: unit test 169 failing\n");
  if(key != 4) printf("BST: unit test 170 failing\n");
  if(a.pred(3,&key) != &v2) printf("BST: unit test 171 failing\n");
  if(key != 2) printf("BST: unit test 172 failing\n");
  // 4
  if(b.pred(4,&key) != &v6) printf("BST: unit test 173 failing\n");
  if(key != 6) printf("BST: unit test 174 failing\n");
  if(a.pred(4,&key) != &v2) printf("BST: unit test 175 failing\n");
  if(key != 2) printf("BST: unit test 176 failing\n");
  // 5
  if(b.pred(5,&key) != &v6) printf("BST: unit test 177 failing\n");
  if(key != 6) printf("BST: unit test 178 failing\n");
  if(a.pred(5,&key) != &v4) printf("BST: unit test 179 failing\n");
  if(key != 4) printf("BST: unit test 180 failing\n");
  // 6
  if(b.pred(6,&key) != &v8) printf("BST: unit test 181 failing\n");
  if(key != 8) printf("BST: unit test 182 failing\n");
  if(a.pred(6,&key) != &v4) printf("BST: unit test 183 failing\n");
  if(key != 4) printf("BST: unit test 184 failing\n");
  // 7
  if(b.pred(7,&key) != &v8) printf("BST: unit test 185 failing\n");
  if(key != 8) printf("BST: unit test 186 failing\n");
  if(a.pred(7,&key) != &v6) printf("BST: unit test 187 failing\n");
  if(key != 6) printf("BST: unit test 188 failing\n");
  // 8
  if(b.pred(8,&key) != nullptr) printf("BST: unit test 189 failing\n");
  if(a.pred(8,&key) != &v6) printf("BST: unit test 190 failing\n");
  if(key != 6) printf("BST: unit test 191 failing\n");
  // 10
  if(b.pred(10,&key) != nullptr) printf("BST: unit test 192 failing\n");
  if(a.pred(10,&key) != &v8) printf("BST: unit test 193 failing\n");
  if(key != 8) printf("BST: unit test 194 failing\n");
  // delete
  a.del(10);  // should have no impact
  b.del(10);  // should have no impact
  if(!a.check()) printf("BST: unit test 195 failing\n");
  if(!b.check()) printf("BST: unit test 196 failing\n");
  // delete 0
  a.del(0);
  b.del(0);
  if(!a.check()) printf("BST: unit test 197 failing\n");
  if(!b.check()) printf("BST: unit test 198 failing\n");
  if(a.find(0) != nullptr) printf("BST: unit test 199 failing\n");
  if(b.find(0) != nullptr) printf("BST: unit test 199 failing\n");
  if(a.find(-4) != &v4m) printf("BST: unit test 200 failing\n");
  if(b.find(-4) != &v4m) printf("BST: unit test 201 failing\n");
  if(a.find(-2) != &v2m) printf("BST: unit test 202 failing\n");
  if(b.find(-2) != &v2m) printf("BST: unit test 203 failing\n");
  if(a.find(2) != &v2) printf("BST: unit test 204 failing\n");
  if(b.find(2) != &v2) printf("BST: unit test 205 failing\n");
  if(a.find(4) != &v4) printf("BST: unit test 206 failing\n");
  if(b.find(4) != &v4) printf("BST: unit test 207 failing\n");
  if(a.find(6) != &v6) printf("BST: unit test 208 failing\n");
  if(b.find(6) != &v6) printf("BST: unit test 209 failing\n");
  if(a.find(8) != &v8) printf("BST: unit test 210 failing\n");
  if(b.find(8) != &v8) printf("BST: unit test 211 failing\n");
  // delete 8
  a.del(8);
  b.del(8);
  if(!a.check()) printf("BST: unit test 212 failing\n");
  if(!b.check()) printf("BST: unit test 213 failing\n");
  if(a.find(8) != nullptr) printf("BST: unit test 214 failing\n");
  if(b.find(8) != nullptr) printf("BST: unit test 215 failing\n");
  if(a.find(-4) != &v4m) printf("BST: unit test 216 failing\n");
  if(b.find(-4) != &v4m) printf("BST: unit test 217 failing\n");
  if(a.find(-2) != &v2m) printf("BST: unit test 218 failing\n");
  if(b.find(-2) != &v2m) printf("BST: unit test 219 failing\n");
  if(a.find(2) != &v2) printf("BST: unit test 220 failing\n");
  if(b.find(2) != &v2) printf("BST: unit test 221 failing\n");
  if(a.find(4) != &v4) printf("BST: unit test 222 failing\n");
  if(b.find(4) != &v4) printf("BST: unit test 223 failing\n");
  if(a.find(6) != &v6) printf("BST: unit test 224 failing\n");
  if(b.find(6) != &v6) printf("BST: unit test 225 failing\n");
  // delete -4
  a.del(-4);
  b.del(-4);
  if(!a.check()) printf("BST: unit test 226 failing\n");
  if(!b.check()) printf("BST: unit test 227 failing\n");
  if(a.find(-4) != nullptr) printf("BST: unit test 228 failing\n");
  if(b.find(-4) != nullptr) printf("BST: unit test 229 failing\n");
  if(a.find(-2) != &v2m) printf("BST: unit test 230 failing\n");
  if(b.find(-2) != &v2m) printf("BST: unit test 231 failing\n");
  if(a.find(2) != &v2) printf("BST: unit test 232 failing\n");
  if(b.find(2) != &v2) printf("BST: unit test 233 failing\n");
  if(a.find(4) != &v4) printf("BST: unit test 234 failing\n");
  if(b.find(4) != &v4) printf("BST: unit test 235 failing\n");
  if(a.find(6) != &v6) printf("BST: unit test 236 failing\n");
  if(b.find(6) != &v6) printf("BST: unit test 237 failing\n");
  // delete 4
  a.del(4);
  b.del(4);
  if(!a.check()) printf("BST: unit test 238 failing\n");
  if(!b.check()) printf("BST: unit test 239 failing\n");
  if(a.find(-4) != nullptr) printf("BST: unit test 240 failing\n");
  if(b.find(-4) != nullptr) printf("BST: unit test 241 failing\n");
  if(a.find(-2) != &v2m) printf("BST: unit test 242 failing\n");
  if(b.find(-2) != &v2m) printf("BST: unit test 243 failing\n");
  if(a.find(2) != &v2) printf("BST: unit test 244 failing\n");
  if(b.find(2) != &v2) printf("BST: unit test 245 failing\n");
  if(a.find(6) != &v6) printf("BST: unit test 246 failing\n");
  if(b.find(6) != &v6) printf("BST: unit test 247 failing\n");
  // delete 2
  a.del(2);
  b.del(2);
  if(!a.check()) printf("BST: unit test 248 failing\n");
  if(!b.check()) printf("BST: unit test 249 failing\n");
  if(a.find(2) != nullptr) printf("BST: unit test 250 failing\n");
  if(b.find(2) != nullptr) printf("BST: unit test 251 failing\n");
  if(a.find(-2) != &v2m) printf("BST: unit test 252 failing\n");
  if(b.find(-2) != &v2m) printf("BST: unit test 253 failing\n");
  if(a.find(6) != &v6) printf("BST: unit test 254 failing\n");
  if(b.find(6) != &v6) printf("BST: unit test 255 failing\n");
  // delete -2
  a.del(-2);
  b.del(-2);
  if(!a.check()) printf("BST: unit test 256 failing\n");
  if(!b.check()) printf("BST: unit test 257 failing\n");
  if(a.find(-2) != nullptr) printf("BST: unit test 258 failing\n");
  if(b.find(-2) != nullptr) printf("BST: unit test 259 failing\n");
  if(a.find(6) != &v6) printf("BST: unit test 260 failing\n");
  if(b.find(6) != &v6) printf("BST: unit test 261 failing\n");
  // delete 6
  a.del(6);
  b.del(6);
  if(!a.check()) printf("BST: unit test 262 failing\n");
  if(!b.check()) printf("BST: unit test 263 failing\n");
  if(a.find(6) != nullptr) printf("BST: unit test 264 failing\n");
  if(b.find(6) != nullptr) printf("BST: unit test 265 failing\n");

  printf("BST: unit test complete\n");

  return 0;

}
