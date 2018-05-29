class Test {

    public static void main(String[] args){
        System.out.println("main is running");

        A a = new A();
        B b = new B();

        Pair p = new Pair(a,b);
        Pair q = p.setfst(b);
    }
}
class A extends Object { 
    A () { super(); }
}

class B extends Object {
    B () { super(); }
}


class Pair extends Object {
    Object fst;
    Object snd;

    // Constructor
    Pair(Object fst, Object snd) {
        super(); 
        this.fst = fst;
        this.snd = snd;
    }

    // method definition
    Pair setfst(Object newfst) {
        return new Pair(newfst, this.snd);
    }
}
