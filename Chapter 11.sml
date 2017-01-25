(* NOTE: Incomplete, since input from prompt is FUBAR in Poly/ML *)

(* 1 *)

local
fun iconv_a 0 = [] |
    iconv_a i = (append (iconv_a ((i - (i mod 10)) div 10)) ((chr (48+(i mod 10)))::[]))
in
fun iconv i = iconv_a i
end;

local
fun decimals_to_string r 0 = "" |
    decimals_to_string r d = (implode (iconv (floor (r*10.0))))^(decimals_to_string (r*10.0 - (real (floor (r*10.0))))(d-1))
in
fun real_to_str decimals r = (implode (iconv (floor r)))^"."^(decimals_to_string (r - (real (floor r))) decimals)
end;

fun print_r dec r = print(real_to_str dec r);

(* 2 *)
fun prws l_r = print ((fn x => implode (rev (tl (rev (explode x))))) (foldr (fn (r, l)=> r^" "^l) "" (map (real_to_str 2) l_r)));

fun prwrb l_r = print ((fn x => implode (rev (tl (rev (explode x))))) (foldr (fn (r, l)=> r^"\n"^l) "" (map (real_to_str 2) l_r)));

(* 3 *)
local
fun iconv_a 0 = [] |
    iconv_a i = (append (iconv_a ((i - (i mod 10)) div 10)) ((chr (48+(i mod 10)))::[]))
in
fun iconv_alt i = implode (iconv_a i)
end;

local
fun tt n 12 = (iconv_alt n)^" * "^(iconv_alt 12)^" = "^(iconv_alt (n*12)) |
    tt n i = (iconv_alt n)^" * "^(iconv_alt i)^" = "^(iconv_alt (n*i))^"\n"^(tt n (i+1))
in
fun timestable n = print (tt n 1)
end;

(* 4 *)
(* TEST: NONE OF THE BELOW ACTUALLY WORKS. PLEASE DO NOT ATTEMPT TO RUN IT. *)
local
fun mul_10 [] = [] |
    mul_10 (h::t) = (h*10)::(mul_10 t)

fun dconv_a [] list = list |
    dconv_a (h::t) list = (dconv_a t (((ord h)-48)::(mul_10 list)))
in
fun dconv s = foldr (fn (x, y) => x+y) 0 (dconv_a (explode s) [])
end;

local
fun iconv_a 0 = [] |
    iconv_a i = (append (iconv_a ((i - (i mod 10)) div 10)) ((chr (48+(i mod 10)))::[]))
in
fun iconv_alt i = implode (iconv_a i)
end;

fun icount_silly() =
    let val prompt1 = print "1st number: "
    	in
	let val n1 = dconv (Option.valOf(TextIO.inputLine(TextIO.stdIn)))
	in
	let val prompt2 = print "2nd number: "
	in
	let val n2 = dconv (Option.valOf(TextIO.inputLine(TextIO.stdIn)))
	in
	let val result = print(iconv_alt (n1*100 div n2))
	in icount_silly()
	end
	end
	end
	end
	end;
