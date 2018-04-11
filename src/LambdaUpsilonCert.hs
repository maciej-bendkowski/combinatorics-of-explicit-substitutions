module LambdaUpsilonCert where

import qualified Prelude

data Nat =
   O
 | S Nat

minus :: Nat -> Nat -> Nat
minus n m =
  case n of {
   O -> n;
   S k ->
    case m of {
     O -> n;
     S l -> minus k l}}

data Btree =
   Leaf
 | Left Btree
 | Right Btree
 | BNode Btree Btree

data Index =
   Z
 | Succ Index

nat_to_index :: Nat -> Index
nat_to_index n =
  case n of {
   O -> Z;
   S n' -> Succ (nat_to_index n')}

data Term =
   Abs Term
 | Index0 Index
 | App Term Term
 | Closure Term Subs
data Subs =
   Lift Subs
 | Slash Term
 | Shift

lifts :: Nat -> Subs -> Subs
lifts n s =
  case n of {
   O -> s;
   S n' -> Lift (lifts n' s)}

btree_to_term :: Btree -> Term
btree_to_term bt =
  case bt of {
   Leaf -> Index0 Z;
   Left t -> btree_to_term' (S O) t;
   Right t -> Abs (btree_to_term t);
   BNode lt rt -> App (btree_to_term lt) (btree_to_term rt)}

btree_to_term' :: Nat -> Btree -> Term
btree_to_term' n bt =
  case bt of {
   Leaf -> Index0 (nat_to_index n);
   Left t -> btree_to_term' (S n) t;
   Right t -> Closure (btree_to_term t) (lifts (minus n (S O)) Shift);
   BNode lt rt -> Closure (btree_to_term rt)
    (lifts (minus n (S O)) (Slash (btree_to_term lt)))}

