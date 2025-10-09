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
