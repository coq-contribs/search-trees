(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

Require Import search_trees.
Require Import Adding.
Require Import Searching.
Require Import DeleteMax.
Require Import Deleting.
Require Import List2Trees.

Extraction "searchtrees.ml" insert sch rmax rm list2trees list2trees_aux.
                               
