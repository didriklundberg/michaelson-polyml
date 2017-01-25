(* 1a *)
local
fun apn_a [] entry = [entry] |
    apn_a (h::t) n = if h>n
    	      	   	      	   then n::(h::t)
				   else if h=n
				   	then (h::t)
					else h::(apn_a t n)
in
fun add_page_n num list = apn_a list num
end;

(* 1b *)
local
fun awpn_a [] (w2:string, ps2) = [(w2, (ps2::[]))] |
    awpn_a ((w1:string, ps1)::t) (w2, ps2) = if w1>w2
    	      	      then (w2, (ps2::[]))::((w1, ps1)::t)
		      else if w1=w2
			   then (w1, (add_page_n ps2 ps1))::t
			   else (w1, ps1)::(awpn_a t (w2, ps2))
in
fun add_wpage_n wp list = awpn_a list wp
end;

(* 1c *)
datatype entry = word of string | page of int;

local
fun u_i_a [] _ i = i |
    u_i_a ((word w)::t) cpn i = (u_i_a t cpn (add_wpage_n (w, cpn) i)) |
    u_i_a ((page pg)::t) cpn i = (u_i_a t pg i) 
in
fun update_index entry_list index = u_i_a entry_list 0 index 
end;

(* 1d *)
fun index entry_list = update_index entry_list [];

(* 2a *)
datatype park = enter of string | exit of string | time of int;

local
fun addrn_a [] regnr ti = [(regnr, ti)] |
    addrn_a ((reg1:string, time1)::t) reg2 time2 = if reg2<reg1
    	      	   	      	   then (reg2, time2)::((reg1, time1)::t)
				   else (reg1, time1)::(addrn_a t reg2 time2)
in
fun addrn regnr ti list = addrn_a list regnr ti
end;

(* 2b *)
local
fun updatern_a [] regnr ti = [] |
    updatern_a ((reg1:string, time1)::t) reg2 time2 = if reg2=reg1
    	      	   	      	   then ((reg1, (time1+time2))::t)
				   else (reg1, time1)::(updatern_a t reg2 time2)
in
fun updatern regnr ti list = updatern_a list regnr ti
end;

(* 2c *)
fun process_cpl [] _ tup_list = tup_list |
    process_cpl ((time ti)::t) curr_time tup_list = process_cpl t ti tup_list |
    process_cpl ((enter regnr)::t) curr_time tup_list = process_cpl t curr_time (addrn regnr (~curr_time) tup_list) |
    process_cpl ((exit regnr)::t) curr_time tup_list = process_cpl t curr_time (updatern regnr curr_time tup_list);

(* 3a *)
datatype event = car | bus | lorry | time of int * int;


fun convert_vlist ct (nc, nb, nl) [] = (ct, nc, nb, nl)::[] |
    convert_vlist ct (nc, nb, nl) ((car)::vlt) = convert_vlist ct (nc+1, nb, nl) vlt |
    convert_vlist ct (nc, nb, nl) ((bus)::vlt) = convert_vlist ct (nc, nb+1, nl) vlt |
    convert_vlist ct (nc, nb, nl) ((lorry)::vlt) = convert_vlist ct (nc, nb, nl+1) vlt |
    convert_vlist ct (nc, nb, nl) ((time (th, tm))::vlt) = (ct,nc, nb, nl)::(convert_vlist (time (th, tm)) (0, 0, 0) vlt);

(* Task description is a bit contradictory... only makes sense with the below wrapper function*)
fun convert_vlist_common_sense ((time (th, tm))::vlt) = convert_vlist (time (th, tm)) (0, 0, 0) vlt;

(* 3b *)
fun get_no_bus_periods [] = [] |
    get_no_bus_periods ((t, _, 0, _)::slt) = t::(get_no_bus_periods slt) |
    get_no_bus_periods (slh::slt) = get_no_bus_periods slt;

(* 3c *)
fun get_hourly_periods [] = [] |
    get_hourly_periods (((time (th, 00)), nc, nb, nl)::slt) = ((time (th, 00)), nc, nb, nl)::(get_hourly_periods slt) |
    get_hourly_periods (slh::slt) = get_hourly_periods slt;

(* 3d *)
local
fun fp [] _ _ = [] |
    fp (h::t) f pr = if (pr h)
       	      	    then (f h)::(fp t f pr)
		    else h::(fp t f pr)
in
fun apply_f_to_all_ps list f pr = fp list f pr
end;

(* 3e *)
(* Very nonsensical exercise... *)

fun get_no_bus_periods_alt list = apply_f_to_all_ps list (fn (t, nc, nb, nl) => if (nb=0) then (t, nc, nb, nl) else []) (fn (t, nc, nb, nl) => (nb=nb));

(* 4a *)
datatype item = vgn of string * real |
	      	vgt of string * real |
		omn of string * real;

fun get_vegan_items [] = [] |
    get_vegan_items ((vgn item)::slt) = (vgn item)::(get_vegan_items slt) |
    get_vegan_items (slh::slt) = get_vegan_items slt;

(* 4b *)
fun get_omn_items [] = [] |
    get_omn_items ((omn item)::slt) = (omn item)::(get_omn_items slt) |
    get_omn_items (slh::slt) = get_omn_items slt;

local
fun cheapest_it [] curr = curr |
    cheapest_it (omn (name, price)::t) (omn (n2, p2)) = if (price<p2)
    	     	     		       then cheapest_it t (omn (name, price))
				       else cheapest_it t (omn (n2, p2))

fun cheapest (omn (name, price)::t) = cheapest_it t (omn (name, price))

in
fun get_cheapest_omn_item (h::t) = cheapest (get_omn_items (h::t))
end;

(* 4c *)
local
fun get_name (vgn item) = fst item |
    get_name (vgt item) = fst item |
    get_name (omn item) = fst item

fun get_price (vgn item) = snd item |
    get_price (vgt item) = snd item |
    get_price (omn item) = snd item

fun look_up_item_rec [] n = 0.0 | (* exception? *)
    look_up_item_rec (h::t) n = if ((get_name h)=n)
    	     	     		       then (get_price h)
				       else look_up_item_rec t n

in
fun look_up_item list item_name = look_up_item_rec list item_name
end;

(* 4d *)
fun cost_of_order list (order as (o_name, o_quant)) = (real o_quant) * (look_up_item list o_name);

(* 4e *)
fun cost_of_order_list menu_list order_list = foldr (fn (x:real, y:real) => x + y) 0.0 (map (cost_of_order menu_list) order_list);

(* 4f *)
fun cost_of_order_list_lists order_list_lists menu_list = map (cost_of_order_list menu_list) order_list_lists;

(* 5 *)
datatype symbol = STRUE | SFALSE | SAND | SOR | SNOT | LBRA | RBRA;

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

(* 6 *)
datatype polysymbol = PLUS |
	 	     TIMES |
		     POWER |
	    INTEGER of int |
	    VARIABLE of char;

local
fun polylex2 #"+" = PLUS |
    polylex2 #"*" = TIMES |
    polylex2 #"^" = POWER |
    polylex2 h = (VARIABLE h)

and polylex1 [] = [] |
    polylex1 (h::t) = if h >= #"0" andalso h <= #"9"
    	    	  then (polylex3 0 (h::t)) (* send to integer inputting until no more integers *)
		  else (polylex2 h)::(polylex1 t)

and polylex3 i [] = (INTEGER i)::[] |
    polylex3 i (h::t) = if h >= #"0" andalso h <= #"9"
    	     	      then polylex3 ((10*i) + (ord h)-(ord #"0")) t
		      else (INTEGER i)::(polylex1 (h::t)) (* send to normal inputting *)

in
fun polylex s = polylex1 (explode s)
end;

(* 7 *)
datatype progsymbol = PLBRA |
	 	      PRBRA |
		      PPLUS |
		      PMINUS |
		      PTIMES |
		      PDIVIDE |
		      PFUNC |
		      PIMPLIES |
		      PVAR of char |
		      PINT of int;
		      

local
(* symbols of one sign *)
fun proglex2 #"(" = PLBRA |
    proglex2 #")" = PRBRA |
    proglex2 #"+" = PPLUS |
    proglex2 #"-" = PMINUS |
    proglex2 #"*" = PTIMES |
    proglex2 #"/" = PDIVIDE |
    proglex2 h = (PVAR h)    

and proglex1 [] = [] |
    proglex1 (h::(th::[])) = if h >= #"0" andalso h <= #"9"
    	    	  then (proglex3 0 (h::(th::[]))) (* send to integer inputting until no more integers *)
		  else if h = #" "
		       then proglex1 (th::[])
		       else ((proglex2 h)::(proglex1 (th::[]))) |
    proglex1 (h::(th::tt)) = if h >= #"0" andalso h <= #"9"
    	    	  then (proglex3 0 (h::(th::tt))) (* send to integer inputting until no more integers *)
		  else if h = #" "
		       then proglex1 (th::tt)
		       else if h = #"f" andalso th = #"n" (* check for PFUNC *)
		       	    then (PFUNC::(proglex1 tt))
		      	    else if h = #"=" andalso th = #">" (* check for PIMPLES *)
		       	    	 then (PIMPLIES::(proglex1 tt))
		       		 else ((proglex2 h)::(proglex1 (th::tt)))

and proglex3 i [] = (PINT i)::[] |
    proglex3 i (h::t) = if h >= #"0" andalso h <= #"9"
    	     	      then proglex3 ((10*i) + (ord h)-(ord #"0")) t
		      else (PINT i)::(proglex1 (h::t)) (* send to normal inputting *)

in
fun proglex s = proglex1 (explode s)
end;