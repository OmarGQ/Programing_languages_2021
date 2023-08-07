fun change<A>(l2 :: List<A>, flag :: Boolean) -> List<A>:
  cases(List) l2:
    | empty => empty #Returns an empty list if the list is empty
    | link(f, r) => 
      if flag: #when it recives a true, returns the first value and calls itself giving a false
        link(f, change(r, false))
      else: #when it recives a false calls itself giving a true
        change(r, true)
      end
  end
end
 
fun concatenate(l :: List<String>, flag :: Boolean) -> String:
  cases(List) l:
    | empty => "" #Returns an empty string if the list is empty
    | link(f, r) => 
      if flag: #when it recives a true, appens the first string with theresult of calling itself with the rest of the list and a false
        string-append(f, concatenate(r, false))
      else: #when it recives a false calls itself giving a true
        concatenate(r, true)
      end
  end
end

fun sumsquare(n :: Number, last :: Number) -> Number:
  if n <= last: #If the number is smaller or equal to the last value, it square the number and sum it to the result of calling itself giving n+1 and last
    num-expt(n, 2) + sumsquare((n + 1), last)
  else: #Returns 0
    0
  end
end

fun sum-of(l :: List<Number>) -> Number:
  doc: "Compute the sum of the given list of numbers."
  cases(List) l:
    | empty => 0 #Returns 0 if the list is empty
    | link(f, r) => f + sum-of(r)#Sums the first value and the result of calling itself with the rest of the list
  end
where:
  sum-of([list: 1, 2, 3, 4, 5]) is 15
  sum-of([list: 3]) is 3
  sum-of([list: ]) is 0
end


fun alternating<A>(l :: List<A>) -> List<A>:
  doc: "Compute the sub-list of every alternate element, starting with the first."
  change(l, true) #Calls change giving the list and a true
where:
  alternating([list: 1, 2, 3, 4, 5]) is [list: 1, 3, 5]
  alternating([list: "a", "b", "c", "d", "e"]) is [list: "a", "c", "e"]
  alternating([list: "Omar", 21, false, empty]) is [list: "Omar", false]
end


fun alternating-even<A>(l :: List<A>) -> List<A>:
  doc: "Compute the sub-list of every alternate element, starting with the second."
  change(l, false) #Calls change giving the list and a false
where:
  alternating-even([list: 1, 2, 3, 4, 5]) is [list: 2, 4]
  alternating-even([list: "a", "b", "c", "d", "e"]) is [list: "b", "d"]
  alternating-even([list: "Omar", 21, false, empty]) is [list: 21, empty]
end


fun sum-alternating(l :: List<Number>) -> Number:
  doc: "Compute the sum of every alternating element, starting with the first."
  sum-of(change(l, true)) #Calls sum while it calls change as a parameter giving the list and a true
where:
  sum-alternating([list: 1, 2, 3, 4, 5]) is 9
  sum-alternating([list: 1, 2, 3, 4, 5, 6]) is 9
  sum-alternating([list: ]) is 0
  sum-alternating([list: 5]) is 5
end


fun concat-alternating(l :: List<String>) -> String:
  doc: "Concatenate every alternating element."
  concatenate(l, true) #Calls concatenate giving the list and a true
where:
  concat-alternating([list: "O", "b", "m", "d", "a", "", "r"]) is "Omar"
  concat-alternating([list: "b"]) is "b"
  concat-alternating([list: ]) is ""
end


fun sum-of-squares(n :: Number) -> Number:
  doc: "Consumes an integer n and produces the sum of the squares of all numbers from 1 through n.  You may assume that n is at least 1."
  sumsquare(1, n) #Calls sumsquare giving a 1 and the number
where:
  sum-of-squares(1) is 1
  sum-of-squares(6) is 91
end


# NPD = nearest point distance

# Given a list of points, represented "flatly", compute the distance of the one
# nearest from the origin. The input will contain at least one point.

# The input intentionally does not provide a list of pairs, to force the user to 
# decide whether or not to parse. Therefore, there are at least two solution
# structures, depending on whether or not the input is first parsed.

fun dist-2d(x :: Number, y :: Number) -> Number:
  num-sqrt(num-sqr(x) + num-sqr(y)) #Calculates the tangent line to get the distance
  # sqrt(x^2+y^2)=c
end

fun npd(l :: List<Number>) -> Number:
  cases(List) l:
    | empty => 9999 #Returns avery high number if the list is empty
    | link(f, r) =>
      var n1 = dist-2d(f, r.first) #Calculates the distance of the first point
      var n2 = npd(r.rest) #Calls itself and recives the nearest point distance from the rest of the list
      if n1 < n2: #Compares both distances and returns the nearet one
        n1
      else:
        n2
      end
  end
where:
  npd([list: 1, 2, 3, 4]) is%(num-within-rel(0.5)) 2
  npd([list: 8, 3, 1, 7]) is%(num-within-rel(0.5)) 7
  npd([list: 9, 2, 6, 6]) is%(num-within-rel(0.5)) 8
end


# This block is inspired by the kids "crypto" game where you write a
# message in multiple colors and then hold a one-color filter over it;
# the letters of that color disappear leaving the rest visible, and
# hence the message. So you encode relative to the decoder color that
# your recipient has. E.g.:
# http://www.education.com/science-fair/article/colored-filters-send-secret-messages/

data Color: Red | Green | Blue end

data Code:
  | item(letter :: String, color :: Color)
end

type Message = List<Code>

fun decode(msg :: Message, lens-color :: Color) -> String:
  cases(Message) msg:
    | empty => "" #Returns an empty string if the list is empty
    | link(f, r) => 
      if lens-color == f.color: #Compares the item color with lens-color
        decode(r, lens-color) #If they are the same, omits the item and calls itself 
      else:
        string-append(f.letter, decode(r, lens-color)) #If they are not the same, appens the letter and calls itself
      end
  end
where:
  
  decode([list: item("G", Green), item("R", Red), item("B", Blue)], Red) is "GB"
  decode([list: item("G", Blue), item("R", Blue), item("B", Blue)], Blue) is ""
  decode([list: item("O", Red), item("i", Green), item("m", Blue), item("u", Green), item("p", Green), item("a", Red), item("r", Blue)], Green) is "Omar"
end


# Optional challenge:

fun encode(msg :: String, decoder :: Color) -> Message:
  nothing
where:
  true is true
end
