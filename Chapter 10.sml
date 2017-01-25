(* 1a *)

(* Tree datatype. *)
datatype 'a tree = empty | node of 'a * 'a tree * 'a tree;

(* Add to tree. *)
fun add less v empty = node(v, empty, empty) |
    add less v (node(nv, l, r)) = if less v nv
    	       		    	  then node(nv, add less v l, r)
				  else node(nv, l, add less v r);

(* Traverse binary tree *)
fun trav empty = [] |
    trav (node(v, l, r)) = trav l@v::trav r;

(* Less-than check *)
fun less s1 s2 = s1 <= s2;

(* String less-than check *)
fun sless (s1:string) s2 = s1 <= s2;

(* Integer less-than check *)
fun iless (i1:int) i2 = i1 <= i2;

(* Real less-than check *)
fun rless (r1:real) r2 = r1 <= r2;

(* Check if t is found as a subtree in s. *)
fun is_subtree empty empty _ = true |
    is_subtree (node(tv, tl, tr)) empty less = false |
    is_subtree (node(tv, tl, tr)) (node(sv, sl, sr)) less = if tv=sv
    	       		     	  	    	       then (is_subtree tl sl less) andalso (is_subtree tr sr less)
						       else if (less tv sv)
						       	    then (is_subtree (node(tv, tl, tr)) sl less)
							    else (is_subtree (node(tv, tl, tr)) sr less);

(* 1b *)
fun rev_ino_trav empty = [] |
    rev_ino_trav (node(v, l, r)) = (rev_ino_trav r)@(v::(rev_ino_trav l));

(* 1c *)
fun preo_trav empty = [] |
    preo_trav (node(v, l, r)) = v::((preo_trav l)@(preo_trav r));

(* 1d *)
fun poso_trav empty = [] |
    poso_trav (node(v, l, r)) = ((poso_trav l)@(poso_trav r))@(v::[]);

(* 2a *)
local
fun add_s_to_tree_curr (str, tree) = (add sless str tree)
in
fun add_s_to_tree tree = foldr add_s_to_tree_curr empty (map (fn s => s^"s") (trav tree))
end;

(* 2b *)
local
fun double_tree_curr (i, tree) = (add iless i tree)
in
fun double_tree tree = foldr double_tree_curr empty (map (fn i => 2*i) (trav tree))
end;

(* 2c *)
local
fun f_tree_curr less (i, tree) = (add less i tree)
in
fun f_tree tree f less = foldr (f_tree_curr less) empty (map f (trav tree))
end;

(* 2d *)
fun double_tree_alt tree = f_tree tree (fn s => s^"s") sless;

fun add_s_to_tree_alt tree = f_tree tree (fn i => 2*i) iless;

(* 2e *)
fun square_if_tree tree = f_tree tree (fn r => if (r>0.001 andalso r<(~0.001)) then r*r else r) rless;

(* 2f *)
fun add_s_if_tree tree = f_tree tree (fn s => if (hd(rev(explode s)) = #"s") then s else s^"s") sless;

(* 2g *)
fun do_f_if_p_tree tree p f less = f_tree tree (fn s => if (p s) then s else f s) less;

(* 2h *)
fun add_s_tree_alt_two tree = do_f_if_p_tree tree (fn s => true) (fn s => s^"s") sless;

fun double_tree_alt_two tree = do_f_if_p_tree tree (fn i => true) (fn i => 2*i) iless;

fun square_if_tree_alt tree = do_f_if_p_tree tree (fn r => r>0.001 andalso r<(~0.001)) (fn r => r*r) rless;

fun add_s_if_tree_alt tree = do_f_if_p_tree tree (fn s => hd(rev(explode s)) = #"s") (fn s => s^"s") sless;

(* 3a *)
fun merge_stree empty = "" |
    merge_stree (node(v, l, r)) = (merge_stree l)^v^(merge_stree r);

(* 3b *)
fun add_itree empty = 0 |
    add_itree (node(v, l, r)) = (add_itree l)+v+(add_itree r);

(* 3c *)
fun flat_f_tree f d empty = d |
    flat_f_tree f d (node(v, l, r)) = f v (flat_f_tree f d l) (flat_f_tree f d r);

(* 3d *)
fun app_str s1 s2 s3 = s1^s2^s3;
fun add_int i1 i2 i3 = i1 + i2 + i3;

fun merge_stree_alt tree = flat_f_tree app_str "" tree;

fun add_itree_alt tree = flat_f_tree add_int 0 tree;

(* 3e *)
local
fun rev_app l1 l2 l3 = l3@(l1::l2)
in
fun rev_ino_trav_alt tree = flat_f_tree rev_app [] tree;
end;

local
fun preo_app l1 l2 l3 = l1::(l2@l3) 
in
fun preo_trav_alt tree = flat_f_tree preo_app [] tree;
end;

local
fun poso_app l1 l2 l3 = (l2@l3)@(l1::[]) 
in
fun poso_trav_alt tree = flat_f_tree poso_app [] tree;
end;

(* 4 prep *)
datatype arith_symbol = lbra | rbra | add | diff | mult | divide | numb of int;

datatype exp = addexp of exp * exp |
	       diffexp of exp * exp |
	       multexp of exp * exp |
	       divexp of exp * exp |
	       negexp of exp |
	       integer of int |
	       fail;

exception Pfail;

(* Recognize an expression. Returns (parse node, rest). *)
fun exp [] = raise Pfail |
    exp e = let val (t1, r1) = term e (* First, check if e starts with a term, and see that it does not end with + or -.  *)
    	    in
		if r1=[] orelse ((hd r1)<>add andalso (hd r1)<>diff)
		then (t1, r1)
		else let val (t2, r2) = term (tl r1) (*???*) (* if term ended with + or -, then we have an addexp or diffexp. *)
		     in
			if (hd r1)=add
			then (addexp(t1, t2), r2)
			else (diffexp(t1, t2), r2)
		     end
	    end
(* Recognize a term. *)
and term [] = raise Pfail |
    term t = let val (f1, r1) = factor t
    	     in
		if r1=[] orelse (hd r1<>mult andalso hd r1<>divide)
		then (f1, r1)
		else let val (f2, r2) = factor (tl r1) (*???*)
		in
			if hd r1=mult
			then (multexp(f1, f2), r2)
			else (divexp(f1, f2), r2)
		end
	     end
(* Recognize a factor. *)
and factor [] = raise Pfail |
    factor (diff::t) = let val (b1, r1) = base t
    	   	       in (negexp b1, r1)
		       end |
    factor f = base f
(* Recognize a base. *)
and base (numb ii::t) = (integer ii, t) |
    base (lbra::t) = let val (e1, r1) = exp t
    	 	     in
			if r1=[] orelse hd r1<>rbra
			then raise Pfail
			else (e1, tl r1)
			end |
    base _ = raise Pfail;

fun is_arith_exp_parsable expr = let val eval = exp expr
    			       	 in
				 true
				 end
				 handle Pfail => false;




(* 4a,b *)
datatype ssymbol = STRUE | SFALSE | SAND | SOR | SNOT | LBRA | RBRA;

local
fun logiclex2 [] = [] |
    logiclex2 (#"t"::t) = STRUE::(logiclex2 t) |
    logiclex2 (#"f"::t) = SFALSE::(logiclex2 t) |
    logiclex2 (#"^"::t) = SAND::(logiclex2 t) |
    logiclex2 (#"v"::t) = SOR::(logiclex2 t) |
    logiclex2 (#"~"::t) = SNOT::(logiclex2 t) |
    logiclex2 (#"("::t) = LBRA::(logiclex2 t) |
    logiclex2 (#")"::t) = RBRA::(logiclex2 t) 

in
fun logiclex s = logiclex2 (explode s)
end;

datatype sexp = andexp of sexp * sexp |
	       orexp of sexp * sexp |
	       negexp of sexp |
	       boolean of bool |
	       fail;

datatype logic = TRUE |
	       	 FALSE |
		 AND of logic * logic |
		 OR of logic * logic |
		 NOT of logic;

(* Recognize an expression. Returns (parse node, rest). *)
fun exp [] = raise Pfail |
    exp e = let val (t1, r1) = term e (* First, check if e starts with a term, and see that it does not end with + or -.  *)
    	    in
		if r1=[] orelse ((hd r1)<>SAND)
		then (t1, r1)
		else let val (t2, r2) = term (tl r1) (*???*) (* if term ended with + or -, then we have an addexp or diffexp. *)
		     in
			(AND(t1, t2), r2)
		     end
	    end
(* Recognize a term. *)
and term [] = raise Pfail |
    term t = let val (f1, r1) = factor t
    	     in
		if r1=[] orelse (hd r1<>SOR)
		then (f1, r1)
		else let val (f2, r2) = factor (tl r1) (*???*)
		in
			(OR(f1, f2), r2)
		end
	     end
(* Recognize a factor. *)
and factor [] = raise Pfail |
    factor (SNOT::t) = let val (b1, r1) = base t
    	   	       in (NOT b1, r1)
		       end |
    factor f = base f
(* Recognize a base. *)
and base (STRUE::t) = (TRUE, t) |
    base (SFALSE::t) = (FALSE, t) |
    base (LBRA::t) = let val (e1, r1) = exp t
    	 	     in
			if r1=[] orelse hd r1<>RBRA
			then raise Pfail
			else (e1, tl r1)
			end |
    base _ = raise Pfail;

fun is_logic_str_parsable str = let val eval = exp (logiclex str)
    			       	 in
				 true
				 end
				 handle Pfail => false |
				 	Match => false;


fun parse_logic_str str = fst (exp (logiclex str));

(* 4c *)
fun pretty_print_parse_tree TRUE = "TRUE" |
    pretty_print_parse_tree FALSE = "FALSE" |
    pretty_print_parse_tree (AND(a1, a2)) = (pretty_print_parse_tree a1)^" AND "^(pretty_print_parse_tree a2) |
    pretty_print_parse_tree (OR(a1, a2)) = (pretty_print_parse_tree a1)^" OR "^(pretty_print_parse_tree a2) |
    pretty_print_parse_tree (NOT(a)) = "NOT "^(pretty_print_parse_tree a);

(* 4d *)
local
fun ev_exp [] = raise Pfail |
    ev_exp e = let val (t1, r1) = ev_term e
    	    in
		if r1=[] orelse ((hd r1)<>SAND)
		then (t1, r1)
		else let val (t2, r2) = ev_term (tl r1)
		     in
			if (t1 = FALSE)
			then (FALSE, r2)
			else if (t2 = FALSE)
			     then (FALSE, r2)
			     else (TRUE, r2)
		     end
	    end
(* Recognize a term. *)
and ev_term [] = raise Pfail |
    ev_term t = let val (f1, r1) = ev_factor t
    	     in
		if r1=[] orelse (hd r1<>SOR)
		then (f1, r1)
		else let val (f2, r2) = ev_factor (tl r1)
		in
			if (f1 = FALSE)
			then if (f2 = FALSE)
			     then (FALSE, r2)
			     else (TRUE, r2)
			else (TRUE, r2)
		end
	     end
(* Recognize a factor. *)
and ev_factor [] = raise Pfail |
    ev_factor (SNOT::t) = let val (b1, r1) = ev_base t
    	   	       in
			if (b1 = FALSE)
			then (TRUE, r1)
			else (FALSE, r1)
		       end |
    ev_factor f = ev_base f
(* Recognize a base. *)
and ev_base (STRUE::t) = (TRUE, t) |
    ev_base (SFALSE::t) = (FALSE, t) |
    ev_base (LBRA::t) = let val (e1, r1) = ev_exp t
    	 	     in
			if r1=[] orelse hd r1<>RBRA
			then raise Pfail
			else (e1, tl r1)
			end |
    ev_base _ = raise Pfail
in
fun evaluate str = fst (ev_exp (logiclex str))
end;

(* 5a *)
(* From previous exercise: *)
datatype polysymbol = PPLUS |
	 	     PTIMES |
		     PPOWER |
	    PINTEGER of int |
	    PVARIABLE of string;

local
fun polylex2 #"+" = PPLUS |
    polylex2 #"*" = PTIMES |
    polylex2 #"^" = PPOWER

and polylex1 vn [] = if vn<>""
    	     	     then (PVARIABLE vn)::[]
		     else [] |
    polylex1 vn (h::t) = if h >= #"0" andalso h <= #"9"
    	    	  then if vn=""
		       then (polylex3 0 (h::t)) (* send to integer inputting until no more integers *)
		       else (PVARIABLE vn)::(polylex3 0 (h::t))
		  else if h<>(#"+") andalso h<>(#"*") andalso h<>(#"^")
		       then (polylex1 (vn^(str h)) t)
		       else if vn=""
		       	    then (polylex2 h)::(polylex1 "" t)
			    else (PVARIABLE vn)::((polylex2 h)::(polylex1 "" t))

and polylex3 i [] = (PINTEGER i)::[] |
    polylex3 i (h::t) = if h >= #"0" andalso h <= #"9"
    	     	      then polylex3 ((10*i) + (ord h)-(ord #"0")) t
		      else (PINTEGER i)::(polylex1 "" (h::t)) (* send to normal inputting *)

in
fun polylex s = polylex1 "" (explode s)
end;
(**)

datatype polynomial = INTEGER of int |
	 	      NAME of string |
		      POWER of polynomial * polynomial |
		      TIMES of polynomial * polynomial |
		      PLUS of polynomial * polynomial;

(* 5b *)
local
fun p_poly [] = raise Pfail |
    p_poly p = let val (t1, r1) = p_term p
    	    in
		if r1=[]
		then (t1, r1)
		else let val (p1, r2) = p_poly (tl r1)
		     in
			(PLUS(t1, p1), r2)
		     end
	    end
(* Recognize a term. *)
and p_term [] = raise Pfail |
    p_term (PINTEGER(i)::t) = let val (i1, r1) = p_int (PINTEGER(i)::t)
    	   		      in
				if (hd t = PTIMES)
    	   		      	then let val (p1, r2) = p_power (tl t)
			      	     	 in
			      		 (TIMES(i1, p1), r2)
			      		 end
			      	else (i1, r1)
			      end |
    p_term t = p_power t
(* Recognize a power. *)
and p_power [] = raise Pfail |
    p_power p = let val (n1, r1) = p_name p
    	   	       in
			if r1=[]
			then (n1, r1) 
			else let val (i1, r2) = p_int (tl r1)
			     in
				(POWER(n1, i1), r2)
			     end
		       end
(* Recognize an integer. *)
and p_int (PINTEGER(i)::t) = ((INTEGER i), t) |
    p_int _ = raise Pfail
(* Recognize a name. *)
and p_name (PVARIABLE(vname)::t) = ((NAME  vname), t) |
    p_name _ = raise Pfail
in
fun get_poly_tree str = fst (p_poly (polylex str))
end;



(* 5c *)
local
fun is_same _ [] = true |
    is_same name n_list = if (name=(hd n_list))
    	    	 	  then (is_same name (tl n_list))
			  else false
fun all_same_in_list [] = true |
    all_same_in_list list = is_same (hd list) (tl list)
fun get_names (PLUS(term, poly)) = get_names(term)@get_names(poly) |
    get_names (TIMES(int, pow)) = get_names(pow) |
    get_names (POWER(name, int)) = get_names(name) |
    get_names (NAME(name)) = name::[] |
    get_names _ = [];
in
fun is_univariate polytree = all_same_in_list (get_names polytree)
end;

(* 5d *)
fun power i 0 = 1 |
    power i p = i*(power i (p-1));

fun evaluate v (PLUS(term, poly)) = (evaluate v term) + (evaluate v poly) |
    evaluate v (TIMES(int, pow)) = (evaluate v int) * (evaluate v pow) |
    evaluate v (POWER(name, int)) = power (evaluate v name) (evaluate v int) |
    evaluate v (NAME(name)) = v |
    evaluate v (INTEGER(int)) = int;

(* 5e *)
local
fun iconv_a 0 = [] |
    iconv_a i = (append (iconv_a ((i - (i mod 10)) div 10)) ((chr (48+(i mod 10)))::[]))
in
fun iconv i = iconv_a i
end;

fun pp_poly (PLUS(term, poly)) = (pp_poly term)^" + "^(pp_poly poly) |
    pp_poly (TIMES(int, pow)) = (pp_poly int)^"*"^(pp_poly pow) |
    pp_poly (POWER(name, int)) = (pp_poly name)^"^"^(pp_poly int) |
    pp_poly (NAME (name)) = name |
    pp_poly (INTEGER (int)) = implode (iconv int);

(* 5f *)
fun differentiate (PLUS(term, poly)) = (PLUS((differentiate term),(differentiate poly))) |
    differentiate (TIMES(int, pow)) = (TIMES(int, differentiate pow)) |
    differentiate (POWER(name, INTEGER(i))) = (POWER( (TIMES(INTEGER(i), name)), (INTEGER (i-1)) )) |
    differentiate (NAME (name)) = (INTEGER (1)) |
    differentiate (INTEGER (int)) = (INTEGER (0));

(* 6a *)
datatype expression = ECALL of expression * expression * expression |
		      EINTEGER of int |
	 	      ENAME of string |
		      EPLUS |
		      EMINUS |
		      ETIMES |
		      EDIVIDE;

(* 6b *)

(* From earlier exercise: *)
datatype progsymbol = PLBRA | (* One symbol *)
	 	      PRBRA |
		      PPLUS |
		      PMINUS |
		      PTIMES |
		      PDIVIDE |
		      PFUNC | (* Two symbols *)
		      PIMPLIES |
		      PVAR of string |
		      PINT of int |
		      PFAIL; (* Fail state *)
		      
local
(* symbols of one sign *)
fun proglex2 #"(" = PLBRA |
    proglex2 #")" = PRBRA |
    proglex2 #"+" = PPLUS |
    proglex2 #"-" = PMINUS |
    proglex2 #"*" = PTIMES |
    proglex2 #"/" = PDIVIDE |
    proglex2 _ = PFAIL

and proglex1 v [] = if v <>""
    	       	    then (PVAR v)::[]
		    else [] |
    proglex1 v (h::[]) = if h >= #"0" andalso h <= #"9"
    	    	  then if v=""
		       then (proglex3 0 (h::[])) (* send to integer inputting until no more integers *)
		       else (PVAR v)::((proglex3 0 (h::[])))
		  else if (proglex2 h)<>PFAIL
		       then if v=""
		       	    then ((proglex2 h)::[])
			    else (PVAR v)::((proglex2 h)::[])
		       else ((PVAR (v^(str h)))::[])|
    proglex1 v (h::(th::[])) = if h >= #"0" andalso h <= #"9"
    	    	  then if v=""
		       then (proglex3 0 (h::(th::[]))) (* send to integer inputting until no more integers *)
		       else (PVAR v)::((proglex3 0 (h::[])))
		  else if h = #" " (* Note that syntactically, "=>" and "fn" can never end an expression. *)
		       then if v=""
		       	    then proglex1 "" (th::[])
			    else (PVAR v)::(proglex1 "" (th::[]))
		       else if v=""
		       	    then if (proglex2 h)<>PFAIL
			    	 then ((proglex2 h)::(proglex1 "" (th::[])))
			    	 else (proglex1 (str h) (th::[]))
			    else if (proglex2 h)<>PFAIL
			    	 then (PVAR v)::(((proglex2 h)::(proglex1 "" (th::[]))))
				 else (proglex1 (v^(str h)) (th::[])) |
    proglex1 v (h::(th::tt)) = if h >= #"0" andalso h <= #"9"
    	    	  then if v=""
		       then (proglex3 0 (h::(th::tt))) (* send to integer inputting until no more integers *)
		       else (PVAR v)::((proglex3 0 (h::(th::tt))))
		  else if h = #" "
		       then if v=""
		       	    then proglex1 "" (th::tt)
			    else (PVAR v)::(proglex1 "" (th::tt))
		       else if h = #"f" andalso th = #"n" (* check for PFUNC *)
		       	    then if v=""
			    	 then (PFUNC::(proglex1 "" tt))
				 else (PVAR v)::((PFUNC::(proglex1 "" tt)))
		      	    else if h = #"=" andalso th = #">" (* check for PIMPLIES *)
		       	    	 then if v=""
				      then (PIMPLIES::(proglex1 "" tt))
				      else (PVAR v)::((PIMPLIES::(proglex1 "" tt)))
		       		 else if ((proglex2 h)=PFAIL)
				      then proglex1 ((str h)^v) (th::tt)
				      else if v=""
				      	   then ((proglex2 h)::(proglex1 "" (th::tt)))
					   else (PVAR v)::(((proglex2 h)::(proglex1 "" (th::tt))))

and proglex3 i [] = (PINT i)::[] |
    proglex3 i (h::t) = if h >= #"0" andalso h <= #"9"
    	     	      then proglex3 ((10*i) + (ord h)-(ord #"0")) t
		      else (PINT i)::(proglex1 "" (h::t)) (* send to normal inputting *)

in
fun proglex s = proglex1 "" (explode s)
end;

exception Pfail;
(* New stuff: *)
local
(* Recognize an expression. *)
fun p_expr [] = raise Pfail |
    p_expr (PVAR(n)::t) = ((ENAME n), t) |
    p_expr (PINT(i)::t) = ((EINTEGER i), t) |
    p_expr e = p_call e
(* Recognize a call. *)
and p_call [] = raise Pfail |
    (* Function call... *)
    p_call (PLBRA::(PFUNC::((PVAR(n))::(PIMPLIES::(t))))) = let val (c1, r1) = p_expr t
    	   						  in
								let val (c2, r2) = p_expr r1
								in
								((ECALL(fst (p_name ((PVAR(n))::[])), c1, c2), (tl r2)))
								end
							  end |
    (* Operator... *)
    p_call (PLBRA::(PLBRA::(t))) = let val (o1, r1) = p_oper t
    	   			       in
				        let val (c1, r2) = p_expr r1
					in
					  let val (c2, r3) = p_expr (tl r2)
					  in
					  (ECALL(o1, c1, c2), (tl r3))
					  end
					end
				       end
(* Recognize an operator. *)
and p_oper [] = raise Pfail |
    p_oper (PPLUS::t) = ((EPLUS), t) |
    p_oper (PMINUS::t) = ((EMINUS), t) |
    p_oper (PTIMES::t) = ((ETIMES), t) |
    p_oper (PDIVIDE::t) = ((EDIVIDE), t) |
    p_oper _ = raise Pfail
    
(* Recognize an integer. *)
and p_int (PINT(i)::t) = ((EINTEGER i), t) |
    p_int _ = raise Pfail
    
(* Recognize a name. *)
and p_name (PVAR(vname)::t) = ((ENAME  vname), t) |
    p_name _ = raise Pfail
in
fun get_prog_tree str = fst (p_expr (proglex str))
end;

(* 6c *)
local
fun iconv_a 0 = [] |
    iconv_a i = (append (iconv_a ((i - (i mod 10)) div 10)) ((chr (48+(i mod 10)))::[]))
in
fun iconv i = iconv_a i
end;

fun pp_expression (ECALL(ENAME (n), e1, e2)) = "(fn "^(pp_expression (ENAME (n)))^" => "^(pp_expression e1)^" "^(pp_expression e2)^")" | (* Function call *)
    pp_expression (ECALL(o1, e1, e2)) = "(("^(pp_expression o1)^" "^(pp_expression e1)^") "^(pp_expression e2)^")" | (* Operator *)
    pp_expression (EINTEGER (i)) = implode (iconv i) |
    pp_expression (ENAME (n)) = n |
    pp_expression (EPLUS) = "+" |
    pp_expression (EMINUS) = "-" |
    pp_expression (ETIMES) = "*" |
    pp_expression (EDIVIDE) = "/";

(* 6d *)
fun names_enc_by_f (ECALL(ENAME (n), e1, e2)) = n::((names_enc_by_f e1)@(names_enc_by_f e2)) | (* Function call *)
    names_enc_by_f (ECALL(o1, e1, e2)) = (names_enc_by_f e1)@(names_enc_by_f e2) | (* Operator *)
    names_enc_by_f _ = [];

local

fun names_outside_f (ECALL(ENAME (n), e1, e2)) = (names_outside_f e1)@(names_outside_f e2) | (* Function call *)
    names_outside_f (ECALL(o1, e1, e2)) = (names_outside_f e1)@(names_outside_f e2) | (* Operator *)
    names_outside_f (ENAME(n)) = n::[] |
    names_outside_f _ = []

fun remove_duplicates [] = [] |
    remove_duplicates (h::t) = if (exists (fn e => h=e) t)
    		      	       then remove_duplicates t
			       else h::(remove_duplicates t);

fun all_elems_not_in_list [] _ = [] |
    all_elems_not_in_list _ [] = [] |
    all_elems_not_in_list (h::t) list = if (exists (fn e => h=e) list)
    			  	      	then all_elems_not_in_list t list
					else h::(all_elems_not_in_list t list)

in
fun no_free_names str = let val inside = names_enc_by_f (get_prog_tree str)
    		      	in
				let val outside = names_outside_f (get_prog_tree str)
				in
				if (length (all_elems_not_in_list (remove_duplicates outside) (remove_duplicates inside))>0)
				then false
				else true
				end
			end
end;

(* 6e *)
local
fun detect_duplicates [] = true |
    detect_duplicates (h::t) = if (exists (fn e => h=e) t)
    			       then false
			       else detect_duplicates t
in
fun unique_f_names str = detect_duplicates (names_enc_by_f (get_prog_tree str))
end;

(* 7f *)
fun repl_inner n r (ECALL(ENAME(nt), e1, e2)) = (ECALL(ENAME(nt), repl_inner n r e1, repl_inner n r e2)) |
    repl_inner n r (ECALL(EPLUS, e1, e2)) = (ECALL(EPLUS, repl_inner n r e1, repl_inner n r e2)) |
    repl_inner n r (ECALL(EMINUS, e1, e2)) = (ECALL(EMINUS, repl_inner n r e1, repl_inner n r e2)) |
    repl_inner n r (ECALL(ETIMES, e1, e2)) = (ECALL(ETIMES, repl_inner n r e1, repl_inner n r e2)) |
    repl_inner n r (ECALL(EDIVIDE, e1, e2)) = (ECALL(EDIVIDE, repl_inner n r e1, repl_inner n r e2)) |
    (* Basal stuff *)
    repl_inner n1 r (ENAME(n2)) = if n1=n2
    	       	    		  then r
				  else (ENAME(n2)) |
    repl_inner n r blah = blah;

fun evaluate (ECALL(EPLUS, e1, e2)) = (evaluate e1) + (evaluate e2) |
    evaluate (ECALL(EMINUS, e1, e2)) = (evaluate e1) - (evaluate e2) |
    evaluate (ECALL(ETIMES, e1, e2)) = (evaluate e1) * (evaluate e2) |
    evaluate (ECALL(EDIVIDE, e1, e2)) = (evaluate e1) div (evaluate e2) |
    evaluate (ECALL(ENAME(n), e1, e2)) = evaluate(repl_inner n (EINTEGER(evaluate e2)) e1) |
    evaluate (EINTEGER(i)) = i;

(* 7e *)
fun evaluate_alt (ECALL(EPLUS, e1, e2)) = (evaluate_alt e1) + (evaluate_alt e2) |
    evaluate_alt (ECALL(EMINUS, e1, e2)) = (evaluate_alt e1) - (evaluate_alt e2) |
    evaluate_alt (ECALL(ETIMES, e1, e2)) = (evaluate_alt e1) * (evaluate_alt e2) |
    evaluate_alt (ECALL(EDIVIDE, e1, e2)) = (evaluate_alt e1) div (evaluate_alt e2) |
    evaluate_alt (ECALL(ENAME(n), e1, e2)) = evaluate_alt(repl_inner n e2 e1) |
    evaluate_alt (EINTEGER(i)) = i;