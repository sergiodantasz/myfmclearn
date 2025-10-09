set_option pp.parens true
set_option autoImplicit false

section A

/-
data Nat
  O : Nat
  S : Nat → Nat

data List α
  Nil : List α
  Cons : α → List α → List α

map : (α → β) → List α → List β
map f [] = []
map f (x :: xs) = f x :: map f xs

filter : (α → Bool) → List α → List α
filter p [] = []
filter p (x :: xs)
  | p x = x :: filter p xs
  | otherwise = filter p xs

length : List α → Nat
length [] = O
length (x :: xs) = S (length xs)

reverse : List α → List α
reverse [] = []
reverse (x :: xs) = reverse xs ⧺ [x]

(⧺) : List α → List α → List α
[] ⧺ xs = xs
(x :: xs) ⧺ ys = x :: (xs ⧺ ys)

sum : List Nat → Nat
sum [] = 0
sum (x :: xs) = x + sum xs

product : List Nat → Nat
product [] = 1
product (x :: xs) = x · product xs
-/

end A

section G

/-
d · (n + m) = d · n + d · m
map f (xs ⧺ ys) = map f xs ⧺ map f ys
product (xs ⧺ ys) = product xs · product ys
reverse (xs ⧺ ys) = reverse ys ⧺ reverse xs
length (xs ⧺ ys) = length xs + length ys
length (map f xs) = length xs
sum (map (+ k) ns) = (sum . map) (+ k) ns
-/

end G
