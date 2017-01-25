(* OMITTED: Exercises 1-4. *)

(* 5a *)

fun intlist 0 = [] |
    intlist n = n::(intlist (n-1));

(* 5b *)

fun sqlist 0 = [] |
    sqlist n = (n*n)::(sqlist (n-1));

(* 5c *)

fun intsqlist 0 = [] |
    intsqlist n = (n, n*n)::(intsqlist (n-1));

(* 5d *)

fun repeat 0 str = [] |
    repeat n str = str::(repeat (n-1) str);

(* 6a *)

fun andlist [] = true |
    andlist (h::t) = h andalso (andlist t);

(* 6b *)

fun sjoin [] = "" |
    sjoin (h::t) = h^(sjoin t);

(* 6c *)

fun spjoin [] = "" |
    spjoin (h::t) = h^" "^(sjoin t);

(* 7a *)

fun poscount [] = 0 |
    poscount (h::t) = if h>0
    	     	      then 1 + poscount t
		      else poscount t;

(* 7b *)

fun more3 [] = 0 |
    more3 (h::t) = if (size h)>3
    	  	   then 1 + more3 t
		   else more3 t;

(* 7c *)

fun countprop _ [] = 0 |
    countprop prop (h::t) = if (prop h)
    	      	   	    then 1 + (countprop prop t)
			    else countprop prop t;

(* 8a *)

fun nonzero [] = true |
    nonzero (h::t) = if not (h=0)
    	     	      then nonzero t
		      else false;

(* 8b *)

fun fourletters [] = true |
    fourletters (h::t) = if (size h)>3
    	     	      then fourletters t
		      else false;

(* 8c *)

fun ful_prop _ [] = true |
    ful_prop prop (h::t) = if prop h
    	     	  	   then ful_prop prop t
			   else false;

(* 8d *)

fun nonzero list = ful_prop (fn n => not (n=0)) list;
fun nonzero list = ful_prop (fn s => (size s)>3) list;

(* 9a *)

fun bigger_fortytwo [] = false |
    bigger_fortytwo (h::t) = if h>42
    		    	     then true
			     else bigger_fortytwo t;

(* 9b *)

fun is_banana [] = false |
    is_banana (h::t) = if h="banana"
    	      	       then true
		       else is_banana t;

(* 9c *)

fun one_ful_prop _ [] = false |
    one_ful_prop prop (h::t) = if prop h
    	     	  	   then true
			   else one_ful_prop prop t;

(* 9d *)

fun bigger_fortytwo_b list = one_ful_prop (fn n => n>42) list;
fun is_banana_b list = one_ful_prop (fn s => s="banana") list;

(* 10a *)

fun dellast [] = [] |
    dellast (h::[]) = [] |
    dellast (h::t) = h::(dellast t);
