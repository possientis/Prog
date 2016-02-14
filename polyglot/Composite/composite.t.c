// included in main file while in development

int String_test(){
  String* x = String_new("Hello World!\n");
  printf("%s",x->buffer);
  String* y = String_copy(x);
  printf("%s",y->buffer);
  String_delete(y);
  String_delete(x);

  String* a = String_new("abc");
  String* b = String_new("def");
  String* c = String_append(a,b);
  printf("%s\n",c->buffer);

  String_delete(c);
  return 0;
}

int ExpInt_test(){

  Environment* env = Environment_new();
  ExpInt* exp = ExpInt_new(34);
  // toString
  String* str = ExpInt_toString(exp);
  printf("exp = %s\n", str->buffer);
  String_delete(str);

  // eval
  Expression* val = ExpInt_eval(exp,env);
  str = Expression_toString(val); 
  printf("val = %s\n", str->buffer);
  String_delete(str);

  // apply
  printf("---------------------------------------------------\n");
  Expression* app = ExpInt_apply(exp,(ExpressionComposite*) val); // makes no sense
  printf("---------------------------------------------------\n");

  // isList
  printf("isList(exp) = %d\n", ExpInt_isList(exp));
  // isInt
  printf("isInt(exp) = %d\n", ExpInt_isInt(exp));


  Expression_delete(val);
  ExpInt_delete(exp);
  Environment_delete(env);


  return 0;
}


int Plus_test(){

  Environment* env = Environment_new();
  Expression* plus = (Expression*) Plus_new();
  Expression* int1 = (Expression*) ExpInt_new(12);
  Expression* int2 = (Expression*) ExpInt_new(13);
  ExpressionComposite* nil = (ExpressionComposite*) Nil_new();
  ExpressionComposite* cons1 = (ExpressionComposite*) Cons_new(int2,nil);
  ExpressionComposite* cons2 = (ExpressionComposite*) Cons_new(int1, cons1);
  Expression* exp = (Expression*) Cons_new(plus, cons2);

  printf("\n");

  // toString
  printf("\n");
  printf("toString: --------------------------------------------------------\n");
  String* str = Expression_toString(exp);
  printf("exp = %s\n", str->buffer);
  String_delete(str);
  printf("------------------------------------------------------------------\n");
  // eval
  printf("\n");
  printf("eval: ------------------------------------------------------------\n");
  Expression* val = Expression_eval(exp,env);
  str = Expression_toString(val);
  printf("val = %s\n", str->buffer);
  String_delete(str);
  Expression_delete(val);
  printf("------------------------------------------------------------------\n");
  // apply
  printf("\n");
  printf("apply: -----------------------------------------------------------\n");
  val = Expression_apply(plus, cons2);
  str = Expression_toString(val);
  printf("val = %s\n", str->buffer);
  String_delete(str);
  printf("------------------------------------------------------------------\n");
  // <------------------------------------------------------------------------ TBI
  // isList
  printf("\n");
  printf("isList -----------------------------------------------------------\n");
  printf("isList(plus) = %d\n", Expression_isList(plus));
  printf("------------------------------------------------------------------\n");
  // isInt
  printf("\n");
  printf("isInt ------------------------------------------------------------\n");
  printf("isInt(plus) = %d\n", Expression_isInt(plus));
  printf("------------------------------------------------------------------\n");

  Expression_delete(val);
  Expression_delete(exp);
  Environment_delete(env);


  return 0;
}

int Mult_test(){

  Environment* env = Environment_new();
  Mult* mult = Mult_new();
  // toString
  printf("\n");
  printf("toString: --------------------------------------------------------\n");
  String* str = Mult_toString(mult);
  printf("mult = %s\n", str->buffer);
  String_delete(str);
  printf("------------------------------------------------------------------\n");
  // eval
  printf("\n");
  printf("eval: ------------------------------------------------------------\n");
  Expression* val = Mult_eval(mult,env);
  str = Expression_toString(val);
  printf("val = %s\n", str->buffer);
  String_delete(str);
  // apply
  printf("\n");
  printf("apply: -----------------------------------------------------------\n");
  printf("apply unit test is not currently implemented\n");
  printf("------------------------------------------------------------------\n");
  // <------------------------------------------------------------------------ TBI
  // isList
  printf("\n");
  printf("isList -----------------------------------------------------------\n");
  printf("isList(mult) = %d\n", Mult_isList(mult));
  printf("------------------------------------------------------------------\n");
  // isInt
  printf("\n");
  printf("isInt ------------------------------------------------------------\n");
  printf("isInt(mult) = %d\n", Mult_isInt(mult));
  printf("------------------------------------------------------------------\n");

  Expression_delete(val);
  Mult_delete(mult);
  Environment_delete(env);


  return 0;
}

int Nil_test(){

  Environment* env = Environment_new();
  Nil*  nil = Nil_new();
  // toString
  printf("\n");
  printf("toString: --------------------------------------------------------\n");
  String* str = Nil_toString(nil);
  printf("nil = %s\n", str->buffer);
  String_delete(str);
  printf("------------------------------------------------------------------\n");
  // eval
  printf("\n");
  printf("eval: ------------------------------------------------------------\n");
  Expression* val = Nil_eval(nil, env);
  str = Expression_toString(val);
  printf("val = %s\n", str->buffer);
  String_delete(str);
  // apply
  printf("\n");
  printf("apply: -----------------------------------------------------------\n");
  Expression* app = Nil_apply(nil,(ExpressionComposite*) val);  // makes no sense
  printf("------------------------------------------------------------------\n");
  // <------------------------------------------------------------------------ TBI
  // isList
  printf("\n");
  printf("isList -----------------------------------------------------------\n");
  printf("isList(nil) = %d\n", Nil_isList(nil));
  printf("------------------------------------------------------------------\n");
  // isInt
  printf("\n");
  printf("isInt ------------------------------------------------------------\n");
  printf("isInt(nil) = %d\n", Nil_isInt(nil));
  printf("------------------------------------------------------------------\n");

  // isNil
  printf("\n");
  printf("isNil ------------------------------------------------------------\n");
  printf("isNil(nil) = %d\n", Nil_isNil(nil));
  printf("------------------------------------------------------------------\n");
 
  // foldLeft
  printf("\n");
  printf("foldLeft ---------------------------------------------------------\n");
  printf("No unit test is currently implemented for foldLeft\n");
  //------------------------------------------------------------------------- TBI
  printf("------------------------------------------------------------------\n");

  // foldRight
  printf("\n");
  printf("foldRight --------------------------------------------------------\n");
  printf("No unit test is currently implemented for foldRight\n");
  //------------------------------------------------------------------------- TBI
  printf("------------------------------------------------------------------\n");

  // evalList
  printf("\n");
  printf("evalList ---------------------------------------------------------\n");
  printf("No unit test is currently implemented for evalList\n");
  //------------------------------------------------------------------------- TBI
  printf("------------------------------------------------------------------\n");

  Expression_delete(val);
  Nil_delete(nil);
  Environment_delete(env);

  return 0;
}

int Cons_test(){

  Environment* env = Environment_new();
  Cons*  cons1 = Cons_new(
      (Expression*) ExpInt_new(45), 
      (ExpressionComposite*) Nil_new()
  );  // cons1 takes over owenership of newly created objects

  printf("\n");
  Cons* cons2 = Cons_new(
      (Expression*) ExpInt_new(55),
      (ExpressionComposite*) cons1
  );  // cons2 takes over ownership of new Int and cons1

  printf("\n");
  Cons* cons = Cons_new(
      (Expression*) Plus_new(),
      (ExpressionComposite*) cons2
  );  // cons takes over ownership of Plus and cons2

  // toString
  printf("\n");
  printf("toString: --------------------------------------------------------\n");
  String* str = Cons_toString(cons);
  printf("cons = %s\n", str->buffer);
  String_delete(str);
  printf("------------------------------------------------------------------\n");
  // eval
  printf("\n");
  printf("eval: ------------------------------------------------------------\n");
  Expression* val = Cons_eval(cons, env);
  assert(val == NULL);
  //str = Expression_toString(val); // <--------------------------------------- TBI
  printf("Cons_eval is not implemented\n");
  //printf("val = %s\n", str->buffer);
  //String_delete(str);
  // apply
  printf("\n");
  printf("apply: -----------------------------------------------------------\n");
  //Expression* app = Nil_apply(nil,(ExpressionComposite*) val);  // makes no sense
  printf("Cons_apply is not implemented\n");
  printf("------------------------------------------------------------------\n");
  // <------------------------------------------------------------------------ TBI
  // isList
  printf("\n");
  printf("isList -----------------------------------------------------------\n");
  printf("isList(cons) = %d\n", Cons_isList(cons));
  printf("------------------------------------------------------------------\n");
  // isInt
  printf("\n");
  printf("isInt ------------------------------------------------------------\n");
  printf("isInt(cons) = %d\n", Cons_isInt(cons));
  printf("------------------------------------------------------------------\n");

  // isNil
  printf("\n");
  printf("isNil ------------------------------------------------------------\n");
  printf("isNil(cons) = %d\n", Cons_isNil(cons));
  printf("------------------------------------------------------------------\n");
 
  // foldLeft
  printf("\n");
  printf("foldLeft ---------------------------------------------------------\n");
  printf("No unit test is currently implemented for foldLeft\n");
  //------------------------------------------------------------------------- TBI
  printf("------------------------------------------------------------------\n");

  // foldRight
  printf("\n");
  printf("foldRight --------------------------------------------------------\n");
  printf("No unit test is currently implemented for foldRight\n");
  //------------------------------------------------------------------------- TBI
  printf("------------------------------------------------------------------\n");

  // evalList
  printf("\n");
  printf("evalList ---------------------------------------------------------\n");
  printf("No unit test is currently implemented for evalList\n");
  //------------------------------------------------------------------------- TBI
  printf("------------------------------------------------------------------\n");

  // Expression_delete(val);
  Cons_delete(cons);
  Environment_delete(env);
  return 0;
}


