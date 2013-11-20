exception EOI
let eoi () = raise EOI

module type INPUT = sig
  type t 
  val next : t -> char
  val set : t -> int -> unit
    
  type from
  val make : from -> t
end

module Location : sig
  type t
  val make : int -> int -> int -> int -> t
  val pp : Format.formatter -> t -> unit
end = struct
  type t = { ls : int; cs : int; le : int; ce : int }
  let make ls cs le ce = { ls; cs; le; ce }
  let pp ppf l = Format.fprintf ppf "[%i:%i-%i:%i]" l.ls l.cs l.le l.ce
end

exception Error of Location.t option
let error loc = raise (Error loc)

exception Missing_entry of string
let missing_entry s = raise (Missing_entry s)

type associativity = Left | Right


module type PARSER = sig
  type 'a t
  type ctx
  val position : ctx -> (int * int)
  type 'a entry
  val fail : 'a t
  val empty : unit t
  val choice : 'a t list -> 'a t
  val eoi : unit t
  val satisfy : (char -> bool) -> char t
  val interval : 'a t -> int -> int -> 'a list t
  val any : char t
  val char : char -> char t
  val string : string -> string t
  val range : char -> char -> char t
  val set : char list -> char t
  val option : 'a t -> 'a option t
  val plus : 'a t -> 'a list t
  val star : 'a t -> 'a list t
  val not : 'a t -> unit t
  val entry : string -> 'a entry
  val add : 'a entry -> 'a t -> unit t
  val rule : ?level:int -> 'a entry -> 'a t
  val junk : 'a t -> unit t
  val parse : ctx -> 'a t -> 'a
  val info : ctx -> ('a, Format.formatter, unit) format -> 'a
  val prefix : 'a t -> int -> 'b entry -> ('a * 'b) t
  val postfix : 'a entry -> 'b t -> int -> ('a * 'b) t
  val infix : 'a entry -> 'b t -> int -> associativity -> 'c entry ->
    ('a * 'b * 'c) t
  val blank : char entry
  val comment : string entry
  val token : 'a t -> ('a * Location.t) t
  type input 
  val make : ?blank:char t -> ?comment:string t -> input -> ctx
  val digit : char t
  val lowercase : char t
  val uppercase : char t
  val letter : char t
  val mk : (ctx -> 'a) -> 'a t
end


let make (type a) (module I : INPUT with type t = a) =
  let module M = struct

    module G = Map.Make(String)
      
    type grammar = exn G.t

    type input = I.t

    type ctx = {
      input : input;
      mutable grammar : grammar;
      mutable index : int;
      mutable line : int;
      mutable column : int;
      mutable out : Format.formatter;
    }

    let save ctx = { ctx with input = ctx.input }
    let load ctx' ctx =
      ctx.grammar <- ctx'.grammar;
      I.set ctx.input ctx'.index;
      ctx.index <- ctx'.index;
      ctx.line <- ctx'.line;
      ctx.column <- ctx'.column

    let next ctx =
      let c = I.next ctx.input in
      begin match c with
      | '\n' ->
	ctx.line <- ctx.line + 1;
	ctx.column <- 0
      | _ ->
	ctx.column <- ctx.column + 1;
      end;
      ctx.index <- ctx.index + 1;
      c

    type _ t =
    | Fail : _ t
    | Empty : unit t
    | Choice : 'a t list -> 'a t
    | Eoi : unit t
    | Satisfy : (char -> bool) -> char t
    | Interval : 'a t * int * int -> 'a list t
    | Any : char t
    | Char : char -> char t
    | String : string -> string t
    | Range : char * char -> char t
    | Set : char list -> char t
    | Option : 'a t -> 'a option t
    | Plus : 'a t -> 'a list t
    | Star : 'a t -> 'a list t
    | Not : 'a t -> unit t
    | Token : 'a t -> ('a * Location.t) t
    | Junk : _ t -> unit t
    | Rule : 'a entry * int -> 'a t
    | Add : 'a entry * 'a t -> unit t
    | Prefix : 'a t * int * 'b entry -> ('a * 'b) t
    | Postfix : 'a entry * 'b t * int -> ('a * 'b) t
    | Infix : 'a entry * 'b t * int * associativity * 'c entry -> ('a * 'b * 'c) t
    | Extern : (ctx -> 'a) -> 'a t

    and 'a memoized = {
      rule : 'a t;
      table : (int, 'a memo) Hashtbl.t;
    }
      
    and 'a memo = NoMemo | Failure | Last of ctx * 'a * int
	
    (* [jb] this part comes from Alain Frisch (on Janestreet's blog about
       universal types). *)
	
    and 'a entry = {
      name : string;
      add : (grammar -> 'a t -> grammar);
      find : (grammar -> 'a memoized);
    }

    let entry (type a) name =
      let module X = struct exception E of a memoized end in
      let find g =
	try
	  match G.find name g with
	  | X.E m -> m
	  | _ ->
  	  (* [jb] may append if someone uses the same name for two physically
  	     different entries.
  	     [jb:todo] just considering it as a misusage for now. I'll
  	     add some exception someday. *)
  	    assert false
	with Not_found -> missing_entry name in
      let add g p =
	let m =
	  try let m = find g in {rule = p; table = m.table}
	  with Missing_entry _ -> {rule = p; table = Hashtbl.create 7} in
	G.add name (X.E m) g in
      { name; add; find }
      
    let lookup m i = try Hashtbl.find m.table i with Not_found -> NoMemo
    let enter m i memo = Hashtbl.replace m.table i memo

    let position ctx = ctx.line, ctx.column

    let fail = Fail
    let empty = Empty
    let choice l = Choice l
    let eoi = Eoi
    let satisfy f = Satisfy f
    let interval p a b = Interval (p, a, b)
    let any = Any
    let char c = Char c
    let string s = String s
    let range a b = Range (a, b)
    let set l = Set l
    let option a = Option a
    let plus a = Plus a
    let star a = Star a
    let not a = Not a
    let digit = range '0' '9'
    let lowercase = range 'a' 'z'
    let uppercase = range 'A' 'Z'
    let letter = choice [ lowercase; uppercase ]
    let junk a = Junk a
    let rule ?(level = 0) a = Rule (a, level)

    let blank = entry "blank"
    let comment = entry "comment"

    let drop_blanks = 
      junk (star (choice [ junk (rule blank); junk (rule comment) ]))
    let token p = Token p
    let add e a = Add (e, a)
    let prefix o lvl e = Prefix (o, lvl, e)
    let postfix e o lvl = Postfix (e, o, lvl)
    let infix l o lvl assoc r = Infix (l, o, lvl, assoc, r)
    let mk f = Extern f

    let info ctx fmt = Format.fprintf ctx.out fmt

    let rec parse : type a. ctx -> a t -> a = fun ctx p ->
      match p with
      | Fail -> error None
      | Empty -> ()
      | Choice l -> parse_choice ctx (save ctx) l
      | Eoi ->
	let sav = save ctx in
	begin 
	  try
	    ignore (next ctx);
	    let l', c' = position ctx in
	    let loc = Location.make sav.line sav.column l' c' in
	    error (Some loc)
	  with EOI -> ()
	end
      | Satisfy f ->
	let l, c = position ctx in
	let res = parse ctx any in
	if Pervasives.not (f res) then begin
	  let l', c' = position ctx in
	  let loc = Location.make l c l' c' in
	  error (Some loc)
	end;
	res
      | Interval (a, i, j) -> parse_interval ctx (save ctx) a i j 0
      | Any ->
	let l, c = position ctx in
	let c =
	  try next ctx
	  with EOI ->
	    let l', c' = position ctx in
	    let loc = Location.make l c l' c' in
	    error (Some loc) in
	c
      | Char c -> parse ctx (satisfy (( = ) c))
      | String s ->
	let l, c = position ctx in
	begin 
	  try
	    for i = 0 to String.length s - 1 do
	      ignore (parse ctx (char s.[i]))
	    done;
	    s
	  with Error _ ->
	    let l', c' = position ctx in
	    let loc = Location.make l c l' c' in
	    error (Some loc)
	end
      | Range (a, b) ->
	let ca = Char.code a in
	let cb = Char.code b in
	let ok c = let cc = Char.code c in ca <= cc && cc <= cb in
	parse ctx (satisfy ok)
      | Set l -> 
	let ok c = List.mem c l in
	parse ctx (satisfy ok)
      | Option a ->
	begin match parse ctx (interval a 0 1) with
	| [] -> None
	| [x] -> Some x
	| _ -> assert false
	end
      | Plus a -> 
	let res = parse ctx (interval a 1 max_int) in
	res
      | Star a -> parse ctx (interval a 0 max_int)
      | Not a ->
	let b, loc = 
	  try ignore (parse ctx a); true, None with Error loc -> false, loc in
	if Pervasives.not b then error loc else ()
      | Junk a -> ignore (parse ctx a)
      | Add (e, a) -> ctx.grammar <- e.add ctx.grammar a
      | Token a ->
	let l, c = position ctx in
	let res = parse ctx a in
	let l', c' = position ctx in
	parse ctx drop_blanks;
	let loc = Location.make l c l' c' in
	res, loc
      | Rule (e, lvl) ->
	let l, c = position ctx in
	begin match parse_rule ctx e lvl with
	| None ->
	  let l', c' = position ctx in
	  let loc = Location.make l c l' c' in
	  error (Some loc)
	| Some x -> x
	end
      | Prefix (o, level, e) ->
	let op = parse ctx o in
	let opand = parse ctx (rule ~level e) in
	op, opand
      | Postfix (e, o, level) ->
	let opand = parse ctx (rule ~level e) in
	let op = parse ctx o in
	opand, op
      | Infix (l, o, level, assoc, r) ->
	let ll, rl = match assoc with
	  | Right -> level, level
	  | Left -> level, level + 1 in
	let lop = parse ctx (rule ~level:ll l) in
	let op = parse ctx o in
	let rop = parse ctx (rule ~level:rl r) in
	lop, op, rop
      | Extern f -> f ctx

    and parse_opt : type a. ctx -> a t -> a option = fun ctx a ->
      try Some (parse ctx a) with Error _ -> None

    and parse_rule : type a.
      ctx -> a entry -> int -> a option = fun ctx e level ->
	let memo = e.find ctx.grammar in
	match lookup memo ctx.index with
	| Failure ->
	(* [jb] this case is special, it is the first iteration and the error is
	   expected but since the state was left intouched, it is no need to
	   save/restore *)
	(* Format.printf ">>> no previous value@."; *)
	  None (* (lvar.3) *)
	|  Last (pre_ctx, pre_prod, pre_lvl) ->
	  (* Format.printf ">>> retrieved %@ (%i, %i)@."
	     pre_ctx.line pre_ctx.column; *)
	  if level < pre_lvl then None (* (lvar.5) *)
	  else begin (* (lvar.4) *)
	    load pre_ctx ctx; (* restore the solution context *)
	    Some pre_prod
	  end
	| NoMemo ->
	  enter memo ctx.index Failure;
	(* [jb] error is expected and we may continue the parsing on the
	   resulting context so we must clone the context for each iteration
  	   of the current fixpoint. *)
	begin
	  let ctx' = save ctx in
	  (* Format.printf ">>> first iteration@."; *)
	  match parse_opt ctx' memo.rule with
	  | None -> 
	    (* Format.printf ">>> failed@."; *)
	    None
	  | Some prod ->
	    (* Format.printf ">>> succeed %@ (%i, %i)@."
	       ctx'.line ctx'.column; *)
	    enter memo ctx.index (Last (ctx', prod, level));
	    let rec increase_bound prod ctx' =
	      let ctx'' = save ctx in
	      match parse_opt ctx'' memo.rule with
	      | Some prod' when ctx''.index > ctx'.index ->
		(* Format.printf ">>> increase to
		   (%i, %i)@." ctx''.line ctx''.column; *)
		enter memo ctx.index (Last (ctx'', prod', level));
		increase_bound prod' ctx'' (* (incr.1) *)
	      | _ -> (* (incr.2) or (incr.3) *)
		(* Format.printf ">>> bound reached!@."; *)
		load ctx' ctx;
		Some (prod)
	    in
	    increase_bound prod ctx'
	end
	  
    and parse_interval : type a.
      ctx -> ctx -> a t -> int -> int -> int -> a list = fun ctx sav p i j k ->
	if k >= j then []
	else
	  let sav' = save ctx in
	  match parse_opt ctx p with
	  | None ->
	    if k < i then 
	      let l, c = position ctx in
	      let loc = Location.make sav.line sav.column l c in
	      error (Some loc)
	    else (load sav' ctx; [])
	  | Some x ->
	  (* we need to check if there was a progression to avoid an infinite
	     loop for some parsers may produce a result even if nothing is
	     consumed (like junk, star, ...). *)
	    if ctx.index <= sav.index then []
	    else
	      let res = parse_interval ctx sav p i j (k + 1) in
	      x :: res
		
    and parse_choice 
      : type a. ctx -> ctx -> a t list -> a =
	  fun ctx sav l ->
	    begin match l with 
	    | [] ->
	      let l, c = position ctx in
	      let loc = Location.make sav.line sav.column l c in
	      error (Some loc)
	    | h :: t ->
	      begin
		try parse ctx h
		with Error _ ->
		  load sav ctx;
		  parse_choice ctx sav t
	      end
	    end

    let blank_entry = blank
    let comment_entry = comment
    
    let make ?(blank = set [' '; '\t'; '\n']) ?(comment = fail) input =
      let ctx = {
	input = input;
	grammar = G.empty;
	index = 0;
	line = 1;
	column = 0;
	out = Format.std_formatter;
      } in
      parse ctx (add blank_entry blank);
      parse ctx (add comment_entry comment);
      parse ctx drop_blanks; (* can't fail *)
      ctx



	      
  end in
  (module M : PARSER with type input = a)


let str l =
  let buf = Buffer.create 126 in
  List.iter (Buffer.add_char buf) l;
  Buffer.contents buf
  

module String : sig
  include INPUT with type from = string
end = struct
  type from = string
  type t = { content : string; mutable index : int }
  let make s = { content = s; index = 0 }
  let next t = 
    try let c = t.content.[t.index] in t.index <- t.index + 1; c
    with Invalid_argument _ -> eoi ()
  let set t i = t.index <- max 0 (min i (String.length t.content))
end

module InChannel : sig
  include INPUT with type from = in_channel
end = struct
  type from = in_channel
  type t = in_channel
  let next t = try input_char t with End_of_file -> eoi ()
  let set t i = seek_in t i
  let make ic = ic
end

module Test (P : PARSER with type input = String.t) = struct
  open Format
  open P

  type 'a result = Ok of 'a | Fail of string
  
  let test p src a =
    let input = String.make src in
    let ctx = P.make input in
    try
      let res = parse ctx p in
      Ok res = a
    with Error (Some loc) ->
      let str =
	Format.fprintf Format.str_formatter "%a" Location.pp loc;
	Format.flush_str_formatter () in
      Fail str = a

  type expr = Int of int | Plus of expr * expr | Mult of expr * expr

  let rec pp ppf = function
    | Int n -> Format.fprintf ppf "%i" n
    | Plus (a, b) -> Format.fprintf ppf "(%a+%a)" pp a pp b
    | Mult (a, b) -> Format.fprintf ppf "(%a*%a)" pp a pp b

  let expr : (expr * Location.t) entry = entry "expr"
    
  let expr_rule =
    token (choice [
      mk (fun ctx ->
	let (l, lloc), (op, lop), (r, rloc) = parse ctx (infix expr (token (char '+')) 50 Left expr) in
	Plus (l, r));
      mk (fun ctx ->
	let (l, lloc), (op, lop), (r, rloc) = parse ctx (infix expr (token (char '*')) 60 Left expr) in
	Mult (l, r));
      mk (fun ctx ->
	let l = parse ctx (plus digit) in
	let i = int_of_string (str l) in
	Int i)
    ])

  let test input expected =
    let i = String.make input in
    let ctx = make i in
    (* info ctx "START HERE@."; *)
    parse ctx (add expr expr_rule);
    try
      let result, loc = parse ctx (rule expr) in
      let str_result =
	Format.fprintf Format.str_formatter "%a" pp result;
	Format.flush_str_formatter () in
      Format.printf "%s : %s %@ %a = %s@."
	input str_result Location.pp loc expected;
      str_result = expected
    with Error (Some loc) ->
      Format.eprintf "parse error near %a@." Location.pp loc;
      false

	  
  let _ =
    assert (test "42" "42");
    assert (test "1 2  7" "1");
    assert (test "1+2" "(1+2)");
    assert (test "1+2+3" "((1+2)+3)");
    assert (test "1*2" "(1*2)");
    assert (test "1*2+3" "((1*2)+3)");
    assert (test "1+2*3" "(1+(2*3))");
    assert (test "1+2*3+4" "((1+(2*3))+4)");
    assert (test "1+ 2  *3 + 4  " "((1+(2*3))+4)");
    assert (test "    1+ 2  *3 + 4  " "((1+(2*3))+4)");
    ()

end

(* module P = (val make (module String) : PARSER with type input = String.t) *)
(* module T = Test(P) *)

module type S = PARSER
