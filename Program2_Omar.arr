use context essentials2021
import s-exp as S
import lists as L

data ArithC: #Collection of basic operations
  | numC(n :: Number)              #Number
  | plusC(l :: ArithC, r :: ArithC)#Sumation
  | multC(l :: ArithC, r :: ArithC)#Multiplication
  | divC(l :: ArithC, r :: ArithC) #Divition
  | modC(l :: ArithC, r :: ArithC) #Modulo
  | expC(l :: ArithC, r :: ArithC) #Exponential
end

data ArithExt: #Collection of advance operations
  | numExt(n :: Number)                    #Number
  | plusExt(l :: ArithExt, r :: ArithExt)  #Sumation
  | multExt(l :: ArithExt, r :: ArithExt)  #Multiplication
  | divExt(l :: ArithExt, r :: ArithExt)   #Divition
  | bminusExt(l :: ArithExt, r :: ArithExt)#Substraction
  | modExt(l :: ArithExt, r :: ArithExt)   #Modulo
  | expExt(l :: ArithExt, r :: ArithExt)   #Exponential
  | rootExt(l :: ArithExt, r :: ArithExt)  #Root
  | uminusExt(e :: ArithExt)               #Negation
  | inverseExt(e :: ArithExt)              #Multiplicative inverse
  | absExt(e :: ArithExt)                  #Absolute value
  | expeExt(e :: ArithExt)                 #e exponential
end

fun parse(s :: S.S-Exp) -> ArithExt: #Transforms a syntax expression into ArthExt
  cases (S.S-Exp) s: #Identifies the syntax expression nd returns its equivalent in ArithExt
    | s-num(n) => numExt(n) #Returns a number when the expression its just a number
    | s-list(shadow s) => #When the expression is more than a number
      cases (List) s:
        | empty => raise("parse: unexpected empty list") #Raises an error if it is empty
        | link(op, args) =>
          len = args.length()   #Gets the number of arguments in the expression
          if len == 1:          #If it has one argument
            arg = L.get(args, 0)#Gets the argument
            ask: #Identifies the operator and returns the expresion in ArthExt
              |op.s == "-" then: uminusExt(parse(arg))
              |op.s == "inv" then: inverseExt(parse(arg))
              |op.s == "abs" then: absExt(parse(arg))
              |op.s == "e^" then: expeExt(parse(arg))
            # |otherwise: raise("Nonexistent operator: " + op.s)
              |otherwise: raise("Nonexistent operator")#Raises an error if the operator does not exist
            end
          else if len == 2:       #If it has two argument
            argL = L.get(args, 0) #Gets both elements
            argR = L.get(args, 1)
            ask: #Identifies the operator and returns the expresion in ArthExt
              |op.s == "+" then: plusExt(parse(argL), parse(argR))
              |op.s == "*" then: multExt(parse(argL), parse(argR))
              |op.s == "-" then: bminusExt(parse(argL), parse(argR))
              |op.s == "/" then: divExt(parse(argL), parse(argR))
              |op.s == "%" then: modExt(parse(argL), parse(argR))
              |op.s == "^" then: expExt(parse(argL), parse(argR))
              |op.s == "root" then: rootExt(parse(argR), parse(argL))
              |otherwise: raise("Nonexistent operator")#Raises an error if the operator does not exist
            end
          else:
            raise("Too many arguments")#Raises an error if the expression has more than two elements
          end
      end
    | else => raise("parse: not number or list")#Raises an error if it recieves an unexpected value
  end
end
check:
  fun p(s): parse(S.read-s-exp(s)) end
  p("(abs -5)") is absExt(numExt(-5))
  p("(- 5)") is uminusExt(numExt(5))
  p("3") is numExt(3)
  p("(+ 1 2)") is plusExt(numExt(1), numExt(2))
  p("(* (+ 1 2) (* 2 5))") is
  multExt(plusExt(numExt(1), numExt(2)), multExt(numExt(2), numExt(5)))
end

fun interp(e :: ArithC) -> Number: #Transforms ArithC into Number
  cases (ArithC) e: #Identifies the ArithC expression and executes de required operations to return a numerical value
    | numC(n) => n
    | plusC(l, r) => interp(l) + interp(r)
    | multC(l, r) => interp(l) * interp(r)
    | divC(l, r) => interp(l) / interp(r) 
    | modC(l, r) => num-modulo(interp(l), interp(r))
    | expC(l, r) => num-expt(interp(l), interp(r))
    | else => raise("Unexpected ArithC expresion")#Raises an error if the expresion does not exist
  end
where:
  interp(numC(3)) is 3
  interp(plusC(numC(3), numC(7))) is 10
  interp(multC(numC(3), numC(7))) is 21
  interp(multC(numC(3), plusC(numC(3), numC(7)))) is 30
  interp(divC(numC(21), numC(4))) is 5.25
  interp(modC(numC(21), numC(4))) is 1
  interp(expC(numC(2), numC(4))) is 16
  interp(divC(numC(1), numC(5))) is 0.20
end

fun desugar(s :: ArithExt) -> ArithC: #Transforms ArithExt into ArithC
  cases (ArithExt) s: #Identifies the ArithExt expression and returns its equivalent in ArithC
    | numExt(n) => numC(n)
    | plusExt(l, r) => plusC(desugar(l), desugar(r))
    | multExt(l, r) => multC(desugar(l), desugar(r))
    | bminusExt(l, r) => plusC(desugar(l), multC(numC(-1), desugar(r)))
    | modExt(l, r) => modC(desugar(l), desugar(r))
    | divExt(l, r) => divC(desugar(l), desugar(r))
    | expExt(l, r) => expC(desugar(l), desugar(r))
    | rootExt(l, r) => expC(desugar(l), divC(numC(1), desugar(r)))
    | expeExt(e) => expC(numC(2.718), desugar(e))
    | uminusExt(e) => multC(numC(-1), desugar(e))
    | inverseExt(e) => divC(numC(1), desugar(e))
    | absExt(e) => expC(multC(desugar(e), desugar(e)), divC(numC(1), numC(2)))
    | else => raise("Unexpected ArithExt expresion") #Raises an error if the expresion does not exist
  end
where:
  desugar(numExt(3)) is numC(3)
  desugar(plusExt(numExt(3), numExt(2))) is plusC(numC(3), numC(2))
  desugar(divExt(numExt(22), numExt(4))) is divC(numC(22), numC(4))
  desugar(bminusExt(multExt(numExt(2), numExt(5)), plusExt(numExt(2), numExt(2)))) is plusC(multC(numC(2), numC(5)), multC(numC(-1), plusC(numC(2), numC(2))))
  desugar(inverseExt(numExt(5))) is divC(numC(1), numC(5))
  desugar(expExt(numExt(5), numExt(2))) is expC(numC(5), numC(2))
  desugar(expeExt(numExt(5))) is expC(numC(2.718), numC(5))
  desugar(rootExt(numExt(25), numExt(2))) is expC(numC(25), divC(numC(1), numC(2)))
end

fun main(s :: String) -> Number:
  interp(desugar(parse(S.read-s-exp(s))))
where:
  main("10") is 10
  main("(+ (* 5 5) (/ 9 3))") is 28
  main("(- 10 (- 10))") is 20
  main("(% 5 3)") is 2
  main("(abs -5)") is 5
  main("(root 2 25)") is 5
  main("(^ 5 2)") is 25
  main("(inv 5)") is 0.2
end