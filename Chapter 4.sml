(* OMITTED: Exercises 1-4. *)

(* 5a *)

fun factorial 0 = 1 |
    factorial n = n*(factorial (n-1));

(* 5b *)

fun pred n = n-1;

fun sub_trololo x 0 = x |
    sub_trololo 0 y = y |
    sub_trololo x y = sub_trololo (pred x) (pred y);

(* 5c *)

fun fib 0 = 0 |
    fib 1 = 1 |
    fib n = (fib (n-1)) + (fib (n-2));

(* 6a *)

fun sjoin 0 str = "" |
    sjoin n str = str^(sjoin (n-1) str);

(* 6b *)

fun ljoin str = sjoin (size str) str;

(* 6c *)

fun rjoin s1 s2 n = s2^(sjoin n s1);

(* 7 *)

fun sumfunc _ 0 = 0 |
    sumfunc f n = f n+sumfunc f (n-1);

(* 7a *)

fun cube 0 = 0 |
    cube n = n*n;

fun sumcube n = sumfunc cube n;

(* 7b *)

fun factorial 0 = 1 |
    factorial n = n*(factorial (n-1));

fun sumfact n = sumfunc factorial n;

(* 7c *)

fun int n = n;

fun sumint n = sumfunc int n;

(* 8a *)

fun max x y = if x>y
    	      then x
	      else y;

(* 8b *)

fun max_real (x:real) (y:real) = if x>y
    	      then x
	      else y;

fun max3 x y z = if x>y
    	       	 then (max_real x z)
		 else (max_real y z);

(* 9 *)

fun is_neg 0 = "zero" |
    is_neg n = if n > 0
    	       then "positive"
	       else "negative";

(* 10a *)

exception divide_by_zero;

fun divide x 0 = raise divide_by_zero |
    divide x y = if x<y
    	       	 then 0
		 else 1 + (divide (x-y) y);

(* 10b *)

fun modulo x y = if x<y
    	       	 then x
		 else modulo (x-y) y;

(* 11a *)

fun extend_space s1 s2 = if (size s1) < (size s2)
    		       	 then extend_space (s1^" ") s2
			 else s1;

(* 11b *)

fun extend s1 s2 s3 = if (size s2) < (size s3)
    		      then extend s1 (s2^s1) s3
		      else s2;

(* 11c *)

fun extend_space_alt s1 s2 = if (size s1) < (size s2)
    		       	     then extend " " (s1^" ") s2
			     else s1;
