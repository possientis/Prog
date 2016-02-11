// included in main file while in development

int String_test(){
  String* x = String_new("Hello World!\n");
  printf("%s",x->buffer);
  String* y = String_copy(x);
  printf("%s",y->buffer);
  String_delete(x);
  String_delete(y);
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
  Plus* plus = Plus_new();
  // toString
  printf("\n");
  printf("toString: --------------------------------------------------------\n");
  String* str = Plus_toString(plus);
  printf("plus = %s\n", str->buffer);
  String_delete(str);
  printf("------------------------------------------------------------------\n");
  // eval
  printf("\n");
  printf("eval: ------------------------------------------------------------\n");
  Expression* val = Plus_eval(plus,env);
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
  printf("isList(plus) = %d\n", Plus_isList(plus));
  printf("------------------------------------------------------------------\n");
  // isInt
  printf("\n");
  printf("isInt ------------------------------------------------------------\n");
  printf("isInt(plus) = %d\n", Plus_isInt(plus));
  printf("------------------------------------------------------------------\n");

  Expression_delete(val);
  Plus_delete(plus);
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


