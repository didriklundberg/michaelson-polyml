~2; (* This is a negative integer. *)
3E3; (* This is 3000.  *)

"This is a string. \
 \Backslash is used to denote line break in a string. \
 \By using backslashes, you can write the characters \\ and \" .";

("This is a tuple", 2);

(* Functions can be prefixes or infixes.  *)

(* Mixed type arithmetic is NOT allowed. *)

(* The "^" joins strings to one another. *)

(* Exercises. First 5 are trivial. *)

(* 6. *)
("a", "a"^"b", "a"^"b"^"c");

("eleven", size "eleven", real (size "eleven"));

(1+1, "one"^"one", 1.0+1.0, true andalso true);

(* 7. *)

(5<size "mulga");

(7>floor 6.54);

real 99 > 89.9;

"fish"^" "^"finger";

";" < "a" orelse ";" > "z";

real 55 * 100.55;

floor (real 77 * 120.23);

(* Continue from h when you have time... *)

