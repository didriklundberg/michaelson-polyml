(* 2a *)

local
fun shortest_a ssf [] = ssf |
    shortest_a ssf (h::t) = if (size h)<(size ssf)
    	       	   	    then shortest_a h t
			    else shortest_a ssf t
in
fun shortest [] = "" |
    shortest (h::t) = shortest_a h t
end;

(* 2b *)

fun culist_a m n = if m>n
    	       	   then []
		   else (m*m*m)::(culist_a  (m+1) n);

(* 2c *)

fun flist f m n = if m>n
    	       	   then []
		   else (f m)::(flist f (m+1) n);

(* 2d *)

fun culist_b m n = flist (fn n => n*n*n) m n;

(* 2e *)

fun halves m n step = if m>n
    	       	   then []
		   else (m div 2)::(halves (m+step) n step);

(* 2f *)

fun flist_a func (m:int) (n:int) step = if m>n
    	       	   then []
		   else ((func (m)))::(flist_a (func) (m+step) n step);

(* 2g *)

fun halves_a m n step = flist_a (fn n => n div 2) m n step;

fun culist_c m n step = flist_a (fn n => n*n*n) m n step;

fun intlist m n step = flist_a (fn n => n) m n step;

(* 3 *)
local
fun reverse_two list [] = list |
    reverse_two list (h::t) = reverse_two (h::list) t

fun reverse list = reverse_two [] list

fun palin_a [] [] = true |
    palin_a (h::t) (hh::tt) = if hh=h
    	    	   	      then palin_a t tt
			      else false
in
fun palin [] = true |
    palin list = palin_a list (reverse list)
end;

(* 4a *)
local
fun sq_tup n = (n, n*n)
in
fun numsq list = map sq_tup list
end;

(* 4b *)
local
fun odd n = if n mod 2 = 1
    	     then true
	     else false
in
fun odds list = map odd list
end;

(* 4c *)
local
fun size_tup str = (str, (size str))
in
fun sizes list = map size_tup list
end;

(* 5a *)
fun more3 list = filter (fn str => if ((size str)>3) then true else false) list;

(* 5b *)
fun getnegs list = filter (fn n => if (n<0) then true else false) list;

(* 5c *)
(* uses 2c, 2f, 2g *)
local
fun is_even n = if (n mod 2 = 0) then true else false

fun is_div_by_seven n = if (n mod 7 = 0) then true else false

in
fun weird_test n = filter is_div_by_seven (map (fn n => n*n) (intlist 2 n 2))
end;

(* 6a *)
local
fun larger_than x y = x>y
in
fun sortdi list = sort larger_than list
end;

(* 6b *)
local
fun longer_than s1 s2 = (size s1)<(size s2)
in
fun sortas list = sort longer_than list
end;

(* 7a *)
local
fun str_join s1 s2 = s1^s2
in
fun join2 list1 list2 = map2 str_join list1 list2
end;

(* 7b *)
local
fun str_num_tup s n = (s, n)
in
fun zip list1 list2 = map2 str_num_tup list1 list2
end;

(* 8a *)
local
fun add_corr (list1, []) = list1 |
    add_corr ([], list2) = list2 |
    add_corr ((h::t), (hh::tt)) = (h+hh)::(add_corr (t, tt))
in
fun addall (list:int list list) = foldr add_corr [] (list:int list list)
end;

(* 8b *)
local
fun longest_one (l1, l2) = if (length l1)>(length l2)
    	       	    then l1
		    else l2
in
fun longest lists = foldr longest_one [] lists
end;

(* 9a *)
fun growth [] = [] |
    growth (h::[]) = [] |
    growth ((h:real)::(hh::tt)) = (hh- h)::(growth (hh::tt));

(* 9b *)
local
fun growth [] = [] |
    growth (h::[]) = [] |
    growth ((h:real)::(hh::tt)) = (hh- h)::(growth (hh::tt));
in
fun av_w_growth list = (foldr (fn (x, y) => x+y) 0.0 (growth list)) / ((real (length list) - 1.0) / 7.0)
end;

(* 9c *)

fun av_w_growths (lists:real list list) = map av_w_growth lists;

(* 9d *)

fun growth_greater (lists:real list list) = filter (fn list => (av_w_growth list)>=0.3) lists;

(* 9e *)

fun growth_count list = length (filter (fn growth => growth<0.4) list);

(* 9f *)
local
fun level growth avg = if (growth < (avg / 2.0))
    	  	       then "low"
		       else if (growth > (2.0 * avg))
		       	    then "high"
			    else "medium"
in
fun growth_level list = map (fn elem => level elem (av_w_growth list)) list
end;

(* 10a *)
local
fun sum_a curr [] = [] |
    sum_a curr (h::t) = (curr + h)::(sum_a h t)
in
fun sum2 [] = [] |
    sum2 (h::t) = sum_a h t
end;

(* 10b *)
local
fun join_a curr [] = [] |
    join_a curr (h::t) = (curr^h)::(join_a h t)
in
fun join2 [] = [] |
    join2 (h::t) = join_a h t
end;

(* 10c *)
local
fun fun_a curr [] _ = [] |
    fun_a curr (h::t) func = (func curr h)::(fun_a h t func)
in
fun fun2 [] _ = [] |
    fun2 (h::t) func = fun_a h t func
end;

(* 10d *)
local
fun add x y = x + y
in
fun sum2_alt list = fun2 list add
end;

local
fun join x y = x^y
in
fun join2_alt list = fun2 list join
end;

(* 11a *)
fun twicenot0 list = map (fn n => 2*n) (filter (fn n => (n>0)) list);

(* 11b *)
fun pluralmore4 list = map (fn s => s^"s") (filter (fn s => (size s)>4) list);

(* 11c *)
fun f_if_p list func pred = map func (filter pred list);

(* 11d *)
fun twicenot0_alt list = f_if_p list (fn n => 2*n) (fn n => (n>0));

fun pluralmore4_alt list = f_if_p list (fn s => s^"s") (fn s => (size s)>4);

(* 12a *)
local
fun sum_odd_a [] = 0 |
    sum_odd_a (h::t) = h + sum_odd_a t
in
fun sum_odd [] = 0 |
    sum_odd list = sum_odd_a (filter (fn n => (n mod 2 = 1)) list)
end;

(* 12b *)
local
fun sum_gten_a [] = 0 |
    sum_gten_a (h::t) = h + sum_gten_a t
in
fun sum_gten [] = 0 |
    sum_gten list = sum_gten_a (filter (fn n => (n > 10)) list)
end;

(* 12c *)
local
fun sum_pred_a [] = 0 |
    sum_pred_a (h::t) = h + sum_pred_a t
in
fun sum_pred [] _ = 0 |
    sum_pred list pred = sum_pred_a (filter pred list)
end;

(* 12d *)
fun sum_odd_alt list = sum_pred list (fn n => (n mod 2)=1);

fun sum_gten_alt list = sum_pred list (fn n => (n>10));

(* 12e *)
local
fun join_pred_a [] = "" |
    join_pred_a (h::t) = h^(join_pred_a t)
in
fun join_pred [] _ = "" |
    join_pred list pred = join_pred_a (filter pred list)
end;

(* 12f *)
local
fun app_func_pred_a [] _ v = v |
    app_func_pred_a (h::t) func v = func h (app_func_pred_a t func v)
in
fun app_func_pred [] _ _ v = v |
    app_func_pred list pred func v = app_func_pred_a (filter pred list) func v
end;

(* 12e *)
fun add_stupid x y = x + y;

fun join_stupid s1 s2 = s1^s2;

fun sum_odd_alt list =  app_func_pred list (fn n => (n mod 2) = 1) add_stupid 0;

fun sum_gten_alt list =  app_func_pred list (fn n => (n>10)) add_stupid 0;

fun sum_pred_alt list pred =  app_func_pred list pred add_stupid 0;

fun join_pred_alt list pred = app_func_pred list pred join_stupid "";

(* 13a *)
local
fun is_flwd_by_inner curr [] = 0 |
    is_flwd_by_inner curr (h::t) = if curr=1 andalso h=2
    		     	  	   then 1 + is_flwd_by_inner h t
				   else 0 + is_flwd_by_inner h t
in
fun is_flwd_by [] = 0 |
    is_flwd_by (h::t) = is_flwd_by_inner h t
end;

(* 13b *)
local
fun is_flwd_by_inner curr [] v1 v2 = 0 |
    is_flwd_by_inner curr (h::t) v1 v2 = if curr=v1 andalso h=v2
    		     	  	   then 1 + is_flwd_by_inner h t v1 v2
				   else 0 + is_flwd_by_inner h t v1 v2
in
fun is_flwd_by_v [] _ _ = 0 |
    is_flwd_by_v (h::t) v1 v2 = is_flwd_by_inner h t v1 v2
end;

(* 13c *)
fun is_flwd_by_alt list = is_flwd_by_v list 1 2;

(* 13d *)
local
fun odd_flwd_by_even_inner curr [] = 0 |
    odd_flwd_by_even_inner curr (h::t) = if ((curr mod 2)=1) andalso ((h mod 2)=0)
    		     	  	   then 1 + odd_flwd_by_even_inner h t
				   else 0 + odd_flwd_by_even_inner h t
in
fun odd_flwd_by_even [] = 0 |
    odd_flwd_by_even (h::t) = odd_flwd_by_even_inner h t
end;

(* 13e *)
local
fun pred_flwd_inner _ [] _ _ = 0 |
    pred_flwd_inner curr (h::t) p1 p2 = if (p1 curr) andalso (p2 h)
    		    	 	      	then 1 + pred_flwd_inner h t p1 p2
					else 0 + pred_flwd_inner h t p1 p2
in
fun pred_flwd [] _ _ = 0 |
    pred_flwd (h::t) p1 p2 = pred_flwd_inner h t p1 p2
end;

(* 13f *)
fun is_flwd_by_alt list = pred_flwd list (fn n => n=1) (fn n => n=2);

fun is_flwd_by_v_alt list v1 v2 = pred_flwd list (fn n => n=v1) (fn n => n=v2);

fun is_flwd_by_oe_alt list = pred_flwd list (fn n => (n mod 2)=1) (fn n => (n mod 2)=0);