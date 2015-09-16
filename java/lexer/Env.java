package symbols;
import java.util.*;

public class Env {
  private Hashtable<String,Symbol> table;
  protected Env prev;

  public Env(Env p){
    table = new Hashtable<String,Symbol>(); prev = p;
  }

  public void put(String s, Symbol sym){
    table.put(s,sym);
  }

  public Symbol get(String s){
    for(Env e = this; e != null; e = e.prev){
      Symbol found = (Symbol) (e.table.get(s));
      if(found != null) return found;
    }
    return null;
  }
}
