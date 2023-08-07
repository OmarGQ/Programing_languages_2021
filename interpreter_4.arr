use context essentials2021
#Omar I Godinez

import s-exp as S
import lists as L
include from S: is-s-list, is-s-sym end

## ************** CORE DATA TYPES ********************

## Function Definition Types (Extended and Core)
data Store:
  | cellVar(name :: String, value :: Value)
  | cellFun(name :: String, exp :: Value)
end

type Storage = List<Store>
mt-sto = empty
xtnd-sto = link

data ExprExt:
    # Value espressions
  | trueExt
  | falseExt
  | nullExt
  | numExt(n :: Number)
    # Binary Arithmetic expressions
  | plusExt(l :: ExprExt, r :: ExprExt)
  | subExt(l :: ExprExt, r :: ExprExt)
  | multExt(l :: ExprExt, r :: ExprExt)
  | divExt(l :: ExprExt, r :: ExprExt)
  | modExt(l :: ExprExt, r :: ExprExt)
    # Numeric Comparison expressions
  | eqExt(l :: ExprExt, r :: ExprExt)
  | biggerExt(l :: ExprExt, r :: ExprExt)
  | smallerExt(l :: ExprExt, r :: ExprExt)
    # Boolean Operators expressions
  | notExt(e :: ExprExt)
  | andExt(l :: ExprExt, r :: ExprExt) 
  | orExt(l :: ExprExt, r :: ExprExt)
    # Conditionals
  | ifExt(c :: ExprExt, t :: ExprExt, e :: ExprExt)
    # Function expresions
  | idExt(s :: String)
  | lambdaExt(name :: String, arg :: List<String>, body :: ExprExt)
  | appExt(name :: ExprExt, arg :: List<ExprExt>)
    # Box expressions
  | consExt(car :: ExprExt, cdr :: ExprExt)
  | carExt(cons :: ExprExt)
  | cdrExt(cons :: ExprExt)
  | set-carExt(cons :: ExprExt, v :: ExprExt)
  | set-cdrExt(cons :: ExprExt, v :: ExprExt)
    #Begin
  | localExt(def :: List<ExprExt>, begin :: List<ExprExt>)
  | isNullExt(obj :: ExprExt)
  | isConsExt(obj :: ExprExt)
    #Stoking
  | fdExt(name :: String, arg :: List<String>, body :: ExprExt)
  | letExt(name :: String, obj :: ExprExt)
end

data ExprC:
    # Value espressions
  | trueC
  | falseC
  | nullC
  | numC(n :: Number)
    # Binary Arithmetic expressions
  | plusC(l :: ExprC, r :: ExprC)  
  | subC(l :: ExprC, r :: ExprC)
  | multC(l :: ExprC, r :: ExprC)  
  | divC(l :: ExprC, r :: ExprC)   
  | modC(l :: ExprC, r :: ExprC)   
    # Boolean Operators expressions
  | eqC(l :: ExprC, r :: ExprC)
  | biggerC(l :: ExprC, r :: ExprC)
  | smallerC(l :: ExprC, r :: ExprC)
    # Boolean Operators expressions
  | notC(e :: ExprC)
  | andC(argl :: ExprC, argr :: ExprC)
  | orC(argl :: ExprC, argr :: ExprC)
    # Conditional expression
  | ifC(c :: ExprC, t :: ExprC, e :: ExprC)
    # Function expressions
  | idC(s :: String)
  | appC(name :: ExprC, arg :: List<ExprC>)
    # Box expressions
  | consC(b :: ExprC, v :: ExprC)
  | carC(cons :: ExprC)
  | cdrC(cons :: ExprC)
  | set-carC(cons :: ExprC, v :: ExprC)
  | set-cdrC(cons :: ExprC, v :: ExprC)
  | localC(def :: List<ExprC>, begin :: List<ExprC>)
  | isNullC(obj :: ExprC)
  | isConsC(obj :: ExprC)
    #stoking
  | fdC(name :: String, arg :: List<String>, body :: ExprC)
  | letC(name :: String, obj :: ExprC) 
end

##Return type
data Value:
  | NIL
  | numV(n :: Number)
  | boolV(b :: Boolean)
  | closV(f :: ExprC, arg :: List<String>)
  | boxV(car :: Value, cdr :: Value)
end

## ************** DESUGARERS ****************

##Desugar-main identifies if we have just one line expression of a local expresion
fun desugar-main(expr :: ExprExt) -> ExprC:
  cases (ExprExt) expr: ##Identifies if we get a local expression or a single expression
    | localExt(_,_) => desugar-local(expr)
    | else => desugar(expr)
  end
where:
  desugar-main(localExt([list: letExt("c", consExt(numExt(1), numExt(2)))],[list: set-carExt(idExt("c"), numExt(4)), carExt(idExt("c"))])) is localC([list: letC("c", consC(numC(1), numC(2)))], [list: set-carC(idC("c"), numC(4)), carC(idC("c"))])
  desugar-main(carExt(consExt(numExt(1), numExt(2)))) is carC(consC(numC(1), numC(2)))
  desugar-main(isNullExt(nullExt)) is isNullC(nullC)
  desugar-main(isConsExt(consExt(numExt(1), numExt(2)))) is isConsC(consC(numC(1), numC(2)))
  desugar-main(localExt([list: fdExt("sum", [list: "lst"], ifExt(isNullExt(idExt("lst")), numExt(0), plusExt(carExt(idExt("lst")), appExt(idExt("sum"), [list: cdrExt(idExt("lst"))]))))], [list: appExt(idExt("sum"), [list: consExt(numExt(1), consExt(numExt(2), consExt(numExt(3), consExt(numExt(4), nullExt))))])])) is localC([list: fdC("sum", [list: "lst"], ifC(isNullC(idC("lst")), numC(0), plusC(carC(idC("lst")), appC(idC("sum"), [list: cdrC(idC("lst"))]))))], [list: appC(idC("sum"), [list: consC(numC(1), consC(numC(2), consC(numC(3), consC(numC(4), nullC))))])])
end

##Desugars local expression
fun desugar-local(local :: ExprExt%(is-localExt)) -> ExprC%(is-localC):
  def = (local.def).map(desugar) ##Desugars the definitions 
  code = (local.begin).map(desugar)##Desugars the instructions
  localC(def, code) ##Returns a localC expression
end

fun desugar(expr :: ExprExt) -> ExprC: ## Desugar all extended expressions into core expressions
  cases (ExprExt) expr:
    | nullExt => nullC
    | trueExt => trueC
    | falseExt => falseC
    | numExt(n) => numC(n)
    | plusExt(l, r) => plusC(desugar(l), desugar(r))
    | subExt(l, r) => subC(desugar(l), desugar(r))
    | multExt(l, r) => multC(desugar(l), desugar(r))
    | divExt(l, r) => divC(desugar(l), desugar(r))
    | modExt(l , r) => modC(desugar(l), desugar(r))
    | eqExt(l, r) => eqC(desugar(l), desugar(r))
    | biggerExt(l, r) => biggerC(desugar(l), desugar(r))
    | smallerExt(l, r) => smallerC(desugar(l), desugar(r))
    | notExt(e) => notC(desugar(e))
    | andExt(l, r) => andC(desugar(l), desugar(r))
    | orExt(l, r) => orC(desugar(l), desugar(r))
    | ifExt(c,t,e) => ifC(desugar(c), desugar(t), desugar(e))  
    | letExt(name, x) => letC(name, desugar(x))
    | fdExt(name, args, body) => fdC(name, args, desugar(body))
    | lambdaExt(name, arg, body) => fdC(name, arg, desugar(body))
    | consExt(car, cdr) => consC(desugar(car), desugar(cdr))
    | carExt(cons) => carC(desugar(cons))
    | cdrExt(cons) => cdrC(desugar(cons))
    | set-carExt(cons, v) => set-carC(desugar(cons), desugar(v))
    | set-cdrExt(cons, v) => set-cdrC(desugar(cons), desugar(v))
    | isNullExt(obj) => isNullC(desugar(obj))
    | isConsExt(obj) => isConsC(desugar(obj))
    | appExt(name, args) => appC(desugar(name), args.map(desugar))
    | idExt(s) => idC(s)
    | else => raise("desugar: Unexpected expression: " + torepr(expr))
  end
end

## ************** INTERPRETERS **************

##Interp-main identifies if we have just one line expression of a local expression
fun interp-main(expr :: ExprC, stor :: Storage) -> Value:
  cases (ExprC) expr:
    | localC(_,_) => interp-local(expr, stor)
    | else => interp(expr, stor)
  end
where:
  interp-main(localC([list: letC("c", consC(numC(1), numC(2)))], [list: set-carC(idC("c"), numC(4)), carC(idC("c"))]), mt-sto) is numV(4)
  interp-main(carC(consC(numC(1), numC(2))), mt-sto) is numV(1)
  interp-main(isNullC(nullC), mt-sto) is boolV(true)
  interp-main(isConsC(consC(numC(1), numC(2))), mt-sto) is boolV(true)
  interp-main(localC([list: fdC("sum", [list: "lst"], ifC(isNullC(idC("lst")), numC(0), plusC(carC(idC("lst")), appC(idC("sum"), [list: cdrC(idC("lst"))]))))], [list: appC(idC("sum"), [list: consC(numC(1), consC(numC(2), consC(numC(3), consC(numC(4), nullC))))])]), mt-sto) is numV(10)
  interp-main(localC([list: fdC("sum", [list: "lst"], ifC(isNullC(idC("lst")), numC(0), plusC(carC(idC("lst")), appC(idC("sum"), [list: cdrC(idC("lst"))]))))], [list: appC(idC("sum"), [list: consC(numC(1), nullC)])]), mt-sto) is numV(1)
end

##Interprets local expression
fun interp-local(local :: ExprC%(is-localC), store :: Storage) -> Value:
  new-store = stoking(local.def, store) ##Creates an Storage with the initial definitions
  interp-aray(local.begin, new-store) ##interprets the instructions
end

##Interprests and put all definitions into the storage before executing the instructios in Begin
fun stoking(args :: List<ExprC>, stor :: Storage) -> Storage:
  cases (List) args:
    |empty => mt-sto ## Returns empty if the list is empty
    |link(f, r) => ## Takes the first element of the list
      cases (ExprC) f:
        | fdC(name, arg, body) => ##If it is a fdC it storages it as a function
          link(cellFun(name, interp(f, stor)), stoking(r, stor))
        | letC(name, obj) => ##If it is a letC it storages it as a variable
          link(cellVar(name, interp(obj, stor)), stoking(r, stor))
        | else => raise("stoking: unexpected expresion")
      end 
  end
where:
  stoking([list: letC("c", consC(numC(1), numC(2)))], mt-sto) is [list: cellVar("c", boxV(numV(1), numV(2)))]
  stoking([list: letC("a", consC(numC(1), numC(2))), letC("b", consC(numC(3), numC(4))), letC("c", consC(numC(5), numC(6)))], mt-sto) is [list: cellVar("a", boxV(numV(1), numV(2))), cellVar("b", boxV(numV(3), numV(4))), cellVar("c", boxV(numV(5), numV(6)))]
  stoking([list: fdC("sum", [list: "lst"], ifC(isNullC(idC("lst")), numC(0), plusC(carC(idC("lst")), appC(idC("sum"), [list: cdrC(idC("lst"))]))))], mt-sto) is [list: cellFun("sum", closV(ifC(isNullC(idC("lst")), numC(0), plusC(carC(idC("lst")), appC(idC("sum"), [list: cdrC(idC("lst"))]))), [list: "lst"]))]
end

##This functions executes one by one all all instructions in the local expression
fun interp-aray(args :: List<ExprC>, stor :: Storage) -> Value:
  cases (List) args:
    |empty => raise("interp-aray: the last instruction did not return a value") #it expects the last instruction to return a Value 
    |link(f, r) => ## Takes the first instruction of the list
      cases(ExprC) f:
        | set-carC(_, _) => #Sets a new value 
          new-stor = modifying(f, stor)
          interp-aray(r, new-stor)
        | set-cdrC(_, _) => #Sets a new value
          new-stor = modifying(f, stor)
          interp-aray(r, new-stor)
        | appC(name, arg) => ##Calls a declared function
          fd = lookup(name.s, stor)
          new-stor = expandStorage(fd.arg, arg, stor)
          interp(fd.f, new-stor)
        | else => interp(f, stor) ##Executes any other core expression
      end
  end   
end

##This function modifies a box in storage 
fun modifying(exp :: ExprC, stor :: Storage) -> Storage:
  cases(ExprC) exp:
    | set-carC(cons, v) => 
      old-cons = lookup(cons.s, stor) ##Gets the box from the storage
      new-cons = cellVar(cons.s, (boxV(interp(v, stor), old-cons.cdr))) ##Creates a modifyed vertion
      update(cons.s, stor, new-cons, 0) ##Calls update to update the storage
    | set-cdrC(cons, v) => 
      old-cons = lookup(cons.s, stor) ##Gets the box from the storage
      new-cons = cellVar(cons.s, (boxV(old-cons.car, interp(v, stor)))) ##Creates a modifyed vertion
      update(cons.s, stor, new-cons, 0) ##Calls update to update the storage
  end
where:
  stor = [list: cellVar("a", boxV(numV(1), numV(2))), cellVar("b", boxV(numV(3), numV(4))), cellVar("c", boxV(numV(5), numV(6)))]
  modifying(set-carC(idC("a"), numC(0)), stor) is [list: cellVar("a", boxV(numV(0), numV(2))), cellVar("b", boxV(numV(3), numV(4))), cellVar("c", boxV(numV(5), numV(6)))]
  modifying(set-cdrC(idC("a"), numC(0)), stor) is [list: cellVar("a", boxV(numV(1), numV(0))), cellVar("b", boxV(numV(3), numV(4))), cellVar("c", boxV(numV(5), numV(6)))]
end
    
##Main interp that identifies the core expression and calls the correct interp
fun interp(exp :: ExprC, stor :: Storage) -> Value:
  cases (ExprC) exp:
    | numC(n) => numV(n)
    | trueC => boolV(true)
    | falseC => boolV(false)
    | nullC => NIL
    | plusC(_, _) => interp-num-op(exp, stor)
    | multC(_, _) => interp-num-op(exp, stor)
    | subC(_, _) => interp-num-op(exp, stor)
    | divC(_, _) => interp-num-op(exp, stor)
    | modC(_, _) => interp-num-op(exp, stor)
    | eqC(_, _) => interp-num-op(exp, stor)
    | smallerC(_, _) => interp-num-op(exp, stor)
    | biggerC(_, _) => interp-num-op(exp, stor)
    | notC(_) => interp-bool-op(exp, stor)
    | andC(_, _) => interp-bool-op(exp, stor)
    | orC(_, _) => interp-bool-op(exp, stor)
    | isNullC(_) => interp-bool-op(exp, stor)
    | isConsC(_) => interp-bool-op(exp, stor)
    | ifC(c, t, e) =>
      c-val = interp(c, stor)
      if is-boolV(c-val):
        if c-val.b:
          interp(t, stor)
        else:
          interp(e, stor)
        end
      else:
        raise("interp: improperly formatted if, condition does not evaluate to boolean")
      end
    | consC(car, cdr) => 
      car-v = interp(car, stor)
      cdr-v = interp(cdr, stor)
      boxV(car-v, cdr-v)
    | carC(_) => interp-cons-op(exp, stor)
    | cdrC(_) => interp-cons-op(exp, stor)
    | idC(_) => lookup(exp.s, stor)
    | appC(name, arg) =>
      fd = lookup(name.s, stor)
      if is-closV(fd):
        new-stor = expandStorage(fd.arg, arg, stor)
        interp(fd.f, new-stor)
      else:
        raise("interp: invalid function application")
      end
    | fdC(_, arg, body) => closV(body, arg)
  end
end

##This interpreter works with numeric operations
fun interp-num-op(exp :: ExprC, stor :: Storage) -> Value:
  cases (ExprC) exp: 
    | plusC(l, r) =>
      l-v = interp(l, stor) ##Interprets both arguments
      r-v = interp(r, stor)
      if is-numV(l-v) and is-numV(r-v): ##Makes sure both are numbers
        numV(l-v.n + r-v.n) ##Executes the operation and returns the result as a Value
      else:
        raise("interp-num-op: + operator not given two number arguments")
      end
    | multC(l, r) =>
      l-v = interp(l, stor)
      r-v = interp(r, stor)
      if is-numV(l-v) and is-numV(r-v):
        numV(l-v.n * r-v.n)
      else:
        raise("interp-num-op: * operator not given two number arguments")
      end
    | subC(l, r) =>
      l-v = interp(l, stor)
      r-v = interp(r, stor)
      if is-numV(l-v) and is-numV(r-v):
        numV(l-v.n - r-v.n)
      else:
        raise("interp-num-op: - operator not given two number arguments")
      end
    | divC(l, r) =>
      l-v = interp(l, stor)
      r-v = interp(r, stor)
      if is-numV(l-v) and is-numV(r-v):
        numV(l-v.n / r-v.n)
      else:
        raise("interp-num-op: / operator not given two number arguments")
      end
    | modC(l, r) =>
      l-v = interp(l, stor)
      r-v = interp(r, stor)
      if is-numV(l-v) and is-numV(r-v):
        numV(num-modulo(l-v.n, r-v.n))
      else:
        raise("interp-num-op: mod operator not given two number arguments")
      end
    | eqC(l, r) =>
      l-v = interp(l, stor)
      r-v = interp(r, stor)
      if is-numV(l-v) and is-numV(r-v):
        boolV(l-v.n == r-v.n)
      else:
        raise("interp-num-op: == operator not given two number arguments")
      end
    | smallerC(l, r) =>
      l-v = interp(l, stor)
      r-v = interp(r, stor)
      if is-numV(l-v) and is-numV(r-v):
        boolV(l-v.n < r-v.n)
      else:
        raise("interp-num-op: < operator not given two number arguments")
      end
    | biggerC(l, r) =>
      l-v = interp(l, stor)
      r-v = interp(r, stor)
      if is-numV(l-v) and is-numV(r-v):
        boolV(l-v.n > r-v.n)
      else:
        raise("interp-num-op: > operator not given two number arguments")
      end
    | else => raise("interp-num-op: not given an operator that requires numbers")
  end
end

##This interpreter works with boolean operations
fun interp-bool-op(exp :: ExprC, stor :: Storage) -> Value:
  cases (ExprC) exp:
    | notC(e) =>
      e-v = interp(e, stor) ##Interprets the argument
      if is-boolV(e-v): ##Makes sure it is a boolean
        boolV(not(e-v.b)) ##Executes the operation and returns the result as a Value
      else:
        raise("interp-bool-op: not operator not given boolean argument")
      end
    | andC(l, r) =>
      l-v = interp(l, stor)
      r-v = interp(r, stor)
      if is-boolV(l-v) and is-boolV(r-v):
        boolV(l-v.b and r-v.b)
      else:
        raise("interp-bool-op: and operator not given two boolean arguments")
      end
    | orC(l, r) =>
      l-v = interp(l, stor)
      r-v = interp(r, stor)
      if is-boolV(l-v) and is-boolV(r-v):
        boolV(l-v.b or r-v.b)
      else:
        raise("interp-bool-op: or operator not given two boolean arguments")
      end
    | isNullC(obj) =>
      cases(ExprC) obj:
        | nullC => boolV(true)
        | idC(s) =>
          nil = lookup(obj.s, stor)
          if is-NIL(nil):
            boolV(true)
          else:
            boolV(false)
          end
        | else => boolV(false)
      end
    | isConsC(obj) =>
      cases(ExprC) obj:
        | consC(_, _) => boolV(true)
        | idC(s) =>
          box = lookup(obj.s, stor)
          if is-boxV(box):
            boolV(true)
          else:
            boolV(false)
          end
        | else => boolV(false)
      end
    | else => raise("interp-bool-op: not given an operator that requires booleans")
  end
end

##This interpreter works with construction/box operations
fun interp-cons-op(exp :: ExprC, stor :: Storage) -> Value:
  cases (ExprC) exp:
    | carC(cons) =>
      cases(ExprC) cons: ##There are two posible cases, we recive a box or an id
        |consC(car, _) => interp(car, stor) ##Gets the Value inside the box
        |idC(s) => 
          box = lookup(s, stor) ##Gets the box from the storage
          if is-boxV(box): ##Verifies it is a box
            box.car ##Gets the Value inside the box
          else:
            raise("interp-cons-op: not given a cons argument " + torepr(box))
          end
      end
    | cdrC(cons) =>
      cases(ExprC) cons:
        |consC(_, cdr) => interp(cdr, stor)
        |idC(s) => 
          box = lookup(s, stor)
          if is-boxV(box):
            box.cdr
          else:
            raise("interp-cons-op: not given a cons argument " + torepr(box))
          end
      end
  end
where:
  stor = [list: cellVar("a", boxV(numV(1), numV(2))), cellVar("b", boxV(numV(3), numV(4))), cellVar("c", boxV(numV(5), numV(6)))]
  stor2 = [list: cellVar("lst", boxV(numV(1), boxV(numV(2), boxV(numV(3), boxV(numV(4), NIL)))))]
  interp-cons-op(carC(consC(numC(4), numC(5))),stor) is numV(4)
  interp-cons-op(carC(idC("a")),stor) is numV(1)
  interp-cons-op(carC(idC("lst")), stor2) is numV(1)
end

##This function retuns a Value from the storage
fun lookup(id :: String, stor :: Storage) -> Value:
  cases (List) stor:
    | empty => raise("lookup: unbound identifier " + id) ##If it reaches the end of the storage, the Value was not found
    | link(f, r) =>
      cases (Store) f:
        | cellVar(name, value) => ##If we are looking for a variable
          if name == id: ##Compares the ID
            value ##Returns the variable Value
          else:
            lookup(id, r)
          end
        | cellFun(name, exp) => ##If we are looking for a function
          if name == id: ##Compares the ID
            exp ##Returns the function expression
          else:
            lookup(id, r)
          end
      end
  end
end

##This function modifies a Value from the storage
fun update(id :: String, stor :: Storage, v :: Store, count :: Number):
  cases (List) stor:
    | empty => raise("update: unbound identifier " + id) ##If it reaches the end of the storage, the Value was not found
    | link(f, r) =>
      if f.name == id: ##Compares the ID
        split = split-at(count, stor) ##Splits the list before the element that we are looking for
        new-stor = (split.prefix).append([list: v]) ##Adds the new Value to the first part of the list
        new-stor.append((split.suffix).drop(1)) ##Drops the first element of the second part and put them together, making a new storage replacing one element
      else:
        lookup(id, r, v, count + 1)
      end
  end
end

##This function adds new elements to the storage
fun expandStorage(args :: List<String>, val :: List<ExprC>, stor :: Storage) -> Storage:
  cases (List) args:
    |empty => stor ##When it reach the end of the list adds the old Storage
    |link(f, r) => ## Takes the first element to add
      link(cellVar(f, interp(val.get(0), stor)) , expandStorage(r, val.drop(1), stor)) ## Adds it to the Storage and recurs the rest of the list
    |else => raise("expandStorage: args do not contain a list")
  end
end

