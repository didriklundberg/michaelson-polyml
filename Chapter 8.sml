(* 1 *)
fun size_of_str str = length (explode str);

(* 2 *)
local
fun starts1 [] _ = true |
    starts1 _ [] = false |
    starts1 (h1::t1) (h2::t2) = if (h1=h2)
    	    	     	      	then starts1 t1 t2
				else false;
in
fun starts s1 s2 = starts1 (explode s1) (explode s2)
end;

local
fun count_all_a _ [] v = v |
    count_all_a sl1 (sl2 as (_::t)) v = if (starts (implode sl1) (implode sl2))
    		    	    	      then count_all_a sl1 t (v+1)
				      else count_all_a sl1 t v
in
fun count_all s1 s2 = count_all_a (explode s1) (explode s2) 0
end;

(* 3 *)
fun erase_from [] s2 = s2 |
    erase_from (_::t1) (_::t2) = erase_from t1 t2;

local
fun delete_all_a _ [] = [] |
    delete_all_a sl1 (sl2 as (h::t)) = if (starts (implode sl1) (implode sl2))
    		    	    	      then (delete_all_a sl1 (erase_from sl1 sl2))
				      else h::(delete_all_a sl1 t)
in
fun delete_all s1 s2 = implode (delete_all_a (explode s1) (explode s2))
end;

(* 4 *)
local
fun prepend_a [] s2 = s2 |
    prepend_a (h1::t1) (s2 as (h2::t2)) = (h2::(prepend_a t1 (h1::t2)));
in
fun prepend (h1::t1) s2 = prepend_a t1 (h1::s2);
end;

local
fun replace_with_a _ _ [] = [] |
    replace_with_a sl1 sl2 (sl3 as (h::t)) = if (starts (implode sl1) (implode sl3))
    		    	    	      then (prepend sl2 (replace_with_a sl1 sl2 (erase_from sl1 sl3)))
				      else h::(replace_with_a sl1 sl2 t)
in
fun replace_with s1 s2 s3 = implode (replace_with_a (explode s1) (explode s2) (explode s3))
end;

(* 5 *)
local
fun insertafterall_a _ _ [] = [] |
    insertafterall_a sl1 sl2 (sl3 as (h::t)) = if (starts (implode sl2) (implode sl3))
    		    	    	      then (prepend (append sl2 sl1) (insertafterall_a sl1 sl2 (erase_from sl2 sl3)))
				      else h::(insertafterall_a sl1 sl2 t)
in
fun insertafterall s1 s2 s3 = implode (insertafterall_a (explode s1) (explode s2) (explode s3))
end;

(* 6 *)
local
fun insertbeforeall_a _ _ [] = [] |
    insertbeforeall_a sl1 sl2 (sl3 as (h::t)) = if (starts (implode sl2) (implode sl3))
    		    	    	      then (prepend sl1 (prepend sl2 (insertbeforeall_a sl1 sl2 (erase_from sl2 sl3))))
				      else h::(insertbeforeall_a sl1 sl2 t)
in
fun insertbeforeall s1 s2 s3 = implode (insertbeforeall_a (explode s1) (explode s2) (explode s3))
end;

(* 7 *)
local
fun iconv_a 0 = [] |
    iconv_a i = (append (iconv_a ((i - (i mod 10)) div 10)) ((chr (48+(i mod 10)))::[]))
in
fun iconv i = iconv_a i
end;

(* 8 *)
local
fun mul_8 [] = [] |
    mul_8 (h::t) = (h*8)::(mul_8 t)

fun oconv_a [] list = list |
    oconv_a (h::t) list = (oconv_a t (((ord h)-48)::(mul_8 list)))
in
fun oconv s = foldr (fn (x, y) => x+y) 0 (oconv_a (explode s) [])
end;

(* 9 *)
local
fun mul_10 [] = [] |
    mul_10 (h::t) = (h*10)::(mul_10 t)

fun dconv_a [] list = list |
    dconv_a (h::t) list = (dconv_a t (((ord h)-48)::(mul_10 list)))
in
fun dconv s = foldr (fn (x, y) => x+y) 0 (dconv_a (explode s) [])
end;

local
fun extract_number [] num = ((implode num), []) |
    extract_number (h::t) num = if h=(#" ")
    		   	      	then ((implode num), t)
				else if h=(#"#") orelse h=(#"O") orelse h=(#"D")
				     then extract_number t num
				     else extract_number t (append num (h::[]))

fun numbs_a [] l_of_nums = l_of_nums |
    numbs_a strl l_of_nums = if (starts "#D" (implode strl))
    	    	 	     then (uncurry numbs_a) let val (new_num, list) = (extract_number strl [])
			     	  	   	    in (list, (append l_of_nums (("decimal", (dconv new_num))::[])))
						    end
			     else if (starts "#O" (implode strl))
    	    	 	     	  then (uncurry numbs_a) let val (new_num, list) = (extract_number strl [])
			     	  	   	    	 in (list, (append l_of_nums (("octal", (oconv new_num))::[])))
						    	 end
				  else l_of_nums (* Shouldn't get here... *)
in
fun numbs str = numbs_a (explode str) []
end;