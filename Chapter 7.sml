(* 2a *)
local
fun addpair_a [] = [] |
    addpair_a ((a, b)::t) = ((a) + (b))::(addpair_a t)
in
fun addpair list = addpair_a list
end;

(* 2b *)
local
fun joinpair_a [] = [] |
    joinpair_a ((a, b)::t) = ((a)^(b))::(joinpair_a t)
in
fun joinpair list = joinpair_a list
end;

(* 2c *)
local
fun checksize_a [] = [] |
    checksize_a ((a, b)::t) = ((size a)=(b))::(checksize_a t)
in
fun checksize list = checksize_a list
end;

(* 2d *)
fun addpair_alt list = map (fn (a,b) => a+b) list;

fun joinpair_alt list = map (fn (a, b) => a^b) list;

fun checksize_alt list = map (fn (a,b) => (size a)=b) list;

(* 3a *)
local
fun ninsert_a [] entry = [entry] |
    ninsert_a ((a:string, b:string)::t) (c, d) = if b>d
    	      	   	      	   then (c, d)::((a, b)::t)
				   else if b=d andalso a>c
				   	then (c, d)::((a, b)::t)
					else (a, b)::(ninsert_a t (c, d))
in
fun ninsert entry list = ninsert_a list entry
end;

(* 3b *)
fun tup_comp (a, b) (c, d) = (size b)<(size d)

fun nsort list = sort (tup_comp) list;

(* 3c *)
fun name_lengths list = map (fn (a, b) => (size a, size b)) list;

(* 4a *)
local
fun addmark_a name grade [] = (name, grade::[])::[] |
    addmark_a (g1:string, f1:string) (grade:int) (((g2, f2), (grades:int list))::t) = if f2>f1
    	      	   	      	   then ((g1, f1), grade::[])::(((g2, f2), grades)::t)
				   else if f1=f2 andalso g2>g1
				   	then ((g1, f1), grade::[])::((g2, f2), grades)::t
					else if f1=f2 andalso g1=g2
					     then (((g1, f1), (grade::grades))::t)
					     else ((g2, f2), grades)::(addmark_a (g1, f1) grade t)
in
fun addmark name grade list = addmark_a name grade list
end;

(* 4b *)
local
fun same_name (g1, f1) ((g2, f2), grades) = g1=g2 andalso f1=f2
fun get_grades ((name, grades)::t) = grades
in
fun getmarks (g, f) list = get_grades (filter (same_name (g, f)) list)
end;

(* 4c *)
local
fun add_stupid (x, y) = x+y
fun avgmark (name, grades:int list) = (name, (foldr add_stupid 0 grades) div (length grades))
in
fun avmark list = map avgmark list
end;

(* 5a *)
fun lclass (a, b, c, d) = if a=c
    	       	     	  then ("horiz", (a, b, c, d))
			  else if b=d
			       then ("vert", (a, b, c, d))
			       else if (abs (a-c))=(abs (b-d))
			       	    then ("diag", (a, b, c, d))
				    else ("other", (a, b, c, d));

(* 5b *)
fun lclasses list = map lclass;

(* 5c *)
local
fun hpoints_a (a, b, c, d) list = if a>c
    	    	      	      	then hpoints_a (a, b, c+1, d) ((c, b)::list)
				else if c>a
				     then hpoints_a (a+1, b, c, d) ((a, b)::list)
				     else if c=a
				     	  then ((a, b)::list)
					  else []
in
fun hpoints tuple = hpoints_a tuple []
end;

(* 5d *)
local
fun vpoints_a (a, b, c, d) list = if b>d
    	    	      	      	then vpoints_a (a, b, c, d+1) ((c, d)::list)
				else if d>b
				     then vpoints_a (a, b+1, c, d) ((a, b)::list)
				     else if d=b
				     	  then ((a, b)::list)
					  else []
in
fun vpoints tuple = vpoints_a tuple []
end;

(* 5e *)
local
fun points_a final next (a, b, c, d) = if (final (a, b, c, d))
    	      	     	   	  then (a, b)::[]
				  else ((a, b)::(points_a final next (next (a, b, c, d))))
in
fun points final next tuple = if (final tuple)
    	   	      	      then []
			      else points_a final next tuple
end;

(* 5f *)
fun vpoints_alt tuple = points (fn (a, b, c, d) => b=d) (fn (a, b, c, d) => (a, b+1, c, d)) tuple;

fun hpoints_alt tuple = points (fn (a, b, c, d) => a=c) (fn (a, b, c, d) => (a+1, b, c, d)) tuple;

(* 5g *)
fun get_horiz_lines list = map hpoints (map (fn (t, points) => points) (filter (fn (t, points) => t="horiz") list));

(* 6a *)
fun to_seconds (h, m, s) = h*60*60 + m*60 + s;

(* 6b *)
fun from_seconds sec = (sec div (60*60), (sec mod (60*60)) div 60, ((sec mod (60*60)) mod 60) );

(* 6c *)
local
fun park_insert_a [] entry = [entry] |
    park_insert_a ((reg1:string, time1)::t) (reg2:string, time2) = if reg2<reg1
    	      	   	      	   then (reg2, time2)::((reg1, time1)::t)
				   else (reg1, time1)::(park_insert_a t (reg2, time2))
in
fun park_insert entry list = park_insert_a list entry
end;

(* 6d *)
fun time_spent reg_nr exit_time list = (fn (reg_nr3, time)::empty_list => (to_seconds exit_time) - (to_seconds time)) (filter (fn (reg_nr2, time) => reg_nr2=reg_nr) list);

(* 6e *)
local
fun addtime_a (reg_nr:string) time [] = (reg_nr, (from_seconds time))::[] |
    addtime_a (reg_nr1:string) time1 ((reg_nr2, time2)::t) = if reg_nr1=reg_nr2
    	      	   	      	   then ((reg_nr1, from_seconds ((time1)+(to_seconds time2)) )::t)
				   else (reg_nr2, time2)::(addtime_a reg_nr1 time1 t)
in
fun addtime reg_nr time_s list = addtime_a reg_nr time_s list
end;

(* 6f *)
local
fun get_longest_time_a longest [] = longest |
    get_longest_time_a (reg_nr1, time1) ((reg_nr2, time2)::t) = if (to_seconds time1)<(to_seconds time2)
    	      	   	      	   then get_longest_time_a (reg_nr2, time2) t
				   else get_longest_time_a (reg_nr1, time1) t
in
fun get_longest_time list = get_longest_time_a ("FOO 666", (0, 0, 0)) list
end;

(* 7a *)
fun month n = List.nth (["January", "February", "March", "April", "May", "June", "July", "August", "September", "October", "November", "December"], n-1);

(* 7b *)
fun mconv list = map (fn (d, m, y) => (d, month m, y)) list;

(* 7c *)
fun curr_y list year = filter (fn (d, m, y) => y=year) (mconv list);

(* 7d *)
local
fun addval_a valu [] = valu::[] |
    addval_a valu (h::t) = if valu=h
    	      	   	   then (h::t)
			   else (h::(addval_a valu t))
in
fun addval valu list = addval_a valu list
end;

(* 7e *)
fun add_date list (d, m, y) = addval y list;

(* 7f *)
fun unique_years t_list list = map (fn (h::t) => h) (map (add_date t_list) list);

(* 7g *)
local
fun ins_date_a [] date = [date] |
    ins_date_a ((d1, m1, y1)::t) (d2, m2, y2) = if y2<=y1
    	      	   	      	   then if y1=y2 andalso m2>=m1
				   	then if m1=m2 andalso d2<=d1
					     then (d2, m2, y2)::((d1, m1, y1)::t)
					     else (d1, m1, y1)::(ins_date_a t (d2, m2, y2)) (* do not insert*)
					else (d2, m2, y2)::((d1, m1, y1)::t) (* insert *)
				   else (d1, m1, y1)::(ins_date_a t (d2, m2, y2))
in
fun ins_date date list = ins_date_a list date
end;

(* 7h *)
fun count_year year dates = foldr (fn ((d, m, y), prev) => prev+1) 0 (filter (fn (d, m, y) => y=year) dates);

(* 8a *)
fun find_records name list = filter (fn (t, n) => t=name) list;

(* 8b *)
fun find_passed name list = foldr (fn ((t, n), prev) => n+prev) 0 (find_records name list);

(* 8c *)
local
fun insert_vehicle_a v [] = [v] |
    insert_vehicle_a (t1, n1) ((t2:string, n2)::t) = if t2>t1
    	      	   	      	   then (t1, n1)::((t2, n2)::t)
				   else if t2=t1 andalso n1>n2
				   	then (t2, n2)::((t1, n1)::t)
					else if t2=t1
					     then (t1, n1)::((t2, n2)::t)
					     else (t2, n2)::(insert_vehicle_a (t1, n1) t)
in
fun insert_vehicle vehicle list = insert_vehicle_a vehicle list
end;

(* 8d *)
local
fun d_record v [] = [] |
    d_record t_d ((t_l, n_l)::t) = if t_d=t_l
    	     	   	       		  then t
					  else (t_l, n_l)::(d_record t_d t)
in
fun delete_record v l = d_record v l
end;

(* 8e *)
local
fun d_record v [] _ = [] |
    d_record t_d ((t_l, n_l)::t) i = if t_d=t_l
    	     	   	       		  then if i=1
					       then t
					       else (t_l, n_l)::(d_record t_d t (i-1))
					  else (t_l, n_l)::(d_record t_d t i)
in
fun delete_ith_record v l i = d_record v l i
end;

(* 8f *)
local
fun find_n v [] = v |
    find_n (t_d, n_d) ((t_l, n_l)::t) = if n_d<n_l
    	     	   	       		  then (find_n (t_l, n_l) t)
					  else (find_n (t_d, n_d) t)
in
fun find_highest_n l = find_n ("Zeppelin", 0) l
end;

(* 9a *)
fun get_rate wname (cname, erlist) = (fn (r, name)::t => r) (filter (fn (r, name) => name=wname) erlist);

(* 9b *)
fun get_record wname list = (fn h::t => h) (filter (fn (name, rates) => wname=name) list);

(* 9c *)
fun exchange list (curr_f, amount:real, curr_t) = (curr_t, (get_rate curr_t (get_record curr_f list))*amount);

(* 9d *)
fun exchanges req_list rates_list = map (exchange rates_list) req_list;