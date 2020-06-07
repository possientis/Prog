public interface AExp {}

class Num implements AExp {
    public int num;
    public Num (int num) { this.num = num; }
}

class Var implements AExp {
    public String var;
    public Var(String var) { this.var = var; }
}

class Add implements AExp {
    public AExp left;
    public AExp right;
    public Add(AExp left, AExp right)
        { this.left = left; this.right = right; }
}

// ....
