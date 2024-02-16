exception DynamicTypeError of string 
exception WrongType of string;; 

type ide = string;;
type 'v env = (ide * 'v) list;;

type tval =
    | TInt
    | TString
    | TBool
    | FunT of tval * tval 
    | SetT of tval;; 

type expr =
    | CstBool of bool
    | CstInt of int 
    | CstString of string 
    | EqualsString of expr * expr 
    | Den of ide 
    | Add of expr * expr 
    | Sub of expr * expr 
    | Times of expr * expr 
    | Mindi of expr * expr
    | IsZero of expr 
    | Equals of expr * expr 
    | And of expr * expr 
    | Or of expr * expr 
    | Not of expr 
    | IfThenElse of expr * expr * expr
    | Let of ide * expr * expr  
    | Fun of ide * tval * tval * expr  
    | FunR of ide * ide * tval * tval * expr
    | LetRec of ide * ide * tval * tval * expr * expr
    | Call of expr * expr 
    | EmptySet of tval 
    | Singleton of expr * tval
    | Of of tval * expr 
    | Lis of expr list 
    | Intersection of expr * expr 
    | Difference of expr * expr 
    | Insert of expr * expr 
    | Remove of expr * expr 
    | Contains of expr * expr 
    | Union of expr * expr 
    | Maxim of expr 
    | Minim of expr 
    | IssetEmpty of expr
    | Issubset of expr * expr
    | Exists of expr * expr 
    | For_all of expr * expr 
    | Filter of expr * expr
    | Map of expr * expr
    ;;

type evT = 
    | Int of int
    | String of string
    | Bool of bool 
    | Closure of ide * tval * tval * expr * evT env 
    
    | RecClosure of ide * ide * tval * tval * expr * evT env
    | Set of set_val 
    and set_val = 
        | EmptyV 
        | NodeV of evT * set_val;;

let bind env i v = ( i, v ) :: env;;
let rec lookup env x = 
   match env with
   | []        -> failwith (x ^ " not found")
   | (y, v)::r -> if x=y then v else lookup r x;;

let rec typecheck (t : string) (v : evT) : bool = 
match t with
    | "int" -> (match v with 
                | Int _ -> true
                | _ -> false )
    | "string" -> (match v with
                | String _ -> true
                | _ -> false )
    | "bool" -> (match v with 
                | Bool _ -> true
                | _ -> false )
    | "fun" -> (match v with  
                | Closure _ -> true
                | RecClosure _ -> true
                | _ -> false )
    | "Set" -> (match v with  
                | Set _ -> true
                | _ -> false )
    | _ -> failwith "Typechecking dinamico fallito: la stringa non è corretta";;

let check_from_lang_tval (tt : tval) : evT -> bool = 
match tt with
    | TInt                       -> typecheck "int"
    | TString                    -> typecheck "string"
    | TBool                      -> typecheck "bool"
    | FunT(_,_)                  -> typecheck "fun"
    | SetT(_)                    -> typecheck "Set";;


let int_add (n: evT) (m: evT) = 
    match typecheck "int" n, typecheck "int" m, n, m with 
    | true, true, Int a, Int b -> Int(a + b)
    | _, _, _, _                  -> raise (WrongType("Addizione non permessa"));;

let int_sub(n: evT) (m: evT) : evT = 
    match typecheck "int" n, typecheck "int" m, n, m with
    | true, true, Int a, Int b -> Int(a - b)
    | _,_,_,_                  -> raise (WrongType("Sottrazione non permessa"));;

let int_times(n: evT) (m: evT) : evT = 
    match typecheck "int" n, typecheck "int" m, n, m with
    | true, true, Int a, Int b -> Int (a * b)
    | _,_,_,_                  -> raise (WrongType("Moltiplicazione non permessa"));;

let int_mindi (n: evT) (m: evT) : evT =
    match typecheck "int" n, typecheck "int" m, n, m with
    | true, true, Int a, Int b -> if (a < b) then Bool(true) else Bool(false)
    | _,_,_,_                  -> raise (WrongType("Moltiplicazione non permessa"));;

let is_zero(n: evT) : evT = 
    match typecheck "int" n, n with
    | true, Int a -> Bool (a = 0)
    | _,_ -> raise (WrongType("Is_zero non permessa"));;

let int_equals(n: evT) (m: evT) : evT = 
    match typecheck "int" n, typecheck "int" m, n, m with
    | true, true, Int a, Int b -> Bool (a = b)
    | _,_,_,_                  -> raise (WrongType("Uguaglianza tra interi non permessa"));;

let bool_and(n: evT) (m: evT) : evT = 
    match typecheck "bool" n, typecheck "bool" m, n, m with
    | true, true, Bool a, Bool b -> Bool (a && b)
    | _,_,_,_                  -> raise (WrongType("And non permessa"));;

let bool_or(n: evT) (m: evT) : evT = 
    match typecheck "bool" n, typecheck "bool" m, n, m with
    | true, true, Bool a, Bool b -> Bool (a || b)
    | _,_,_,_                  -> raise (WrongType("Or non permessa"));;

let bool_not(n: evT) : evT = 
    match typecheck "bool" n, n with
    | true, Bool a -> Bool (not a)
    | _,_                -> raise (WrongType("Not non permessa"));;

let string_equals(s: evT) (z: evT) : evT = 
    match typecheck "string" s, typecheck "string" z, s, z with
    | true, true, String a, String b -> Bool (a = b)
    | _,_,_,_                  -> raise (WrongType("Uguaglianza tra stringhe non permessa"));;


let rec set_contains (s: set_val) (v: evT) : bool = 
    match s with
    | EmptyV -> false 
    | NodeV (v', _) when v' = v -> true 
    | NodeV (_,s') -> set_contains s' v;;

let rec set_union (s1: set_val) (s2: set_val) : set_val = 
    match s1 with
    | EmptyV -> s2
    | NodeV (v1, s1') ->
                        if set_contains s2 v1
                        then set_union s1' s2 
                        else set_union s1' (NodeV(v1,s2));; 

let rec is_subset (s1: set_val) (s2: set_val) : bool = 
    match s1 with
    | EmptyV -> true 
    | NodeV (v1, s1') ->
                        if set_contains s2 v1 
                        then is_subset s1' s2
                        else false ;; 

let rec set_intersection (s1: set_val) (s2: set_val) : set_val = 
    match s1 with
    | EmptyV -> EmptyV
    | NodeV (v1,s1') ->
                        if set_contains s2 v1 
                        then NodeV(v1, (set_intersection s1' s2)) 
                        else set_intersection s1' s2;; 

let rec set_remove (s: set_val) (v: evT) : set_val =  
    match s with
    | EmptyV -> EmptyV
    | NodeV (v',s') when v' = v -> s' 
    | NodeV (v',s') -> NodeV(v', set_remove s' v);; 

let rec set_difference (s1: set_val) (s2: set_val) : set_val = 
    match (s1, s2) with
    | (EmptyV, EmptyV) -> EmptyV
    |  EmptyV , NodeV (v2, s2') -> set_union s1 s2
    | (NodeV (v1,s1'), NodeV (v2, s2')) ->
                        if set_contains s2 v1 
                            then let s2_new = (set_remove s2 v1) in
                                set_difference s1' s2_new 
                                    else NodeV(v1, (set_difference s1' s2));;

let maxim lis = let rec aux l i = match l with
                    | EmptyV -> i
                    | NodeV (v',s') -> if (v' > i) then aux s' v' else aux s' i in aux lis (Int 0);;

let minim lis = let rec aux l i = match l with
                    | EmptyV -> i
                    | NodeV (v',s') -> if (v' < i) then aux s' v' else aux s' i in aux lis (Int 0);;
let rec contain e l = 
  match l with
  | [] -> false
  | hd::tl -> if hd = e then true else contain e tl;;

let rec converti_lista (s : set_val) : evT list =
    match s with
    | EmptyV -> []
    | NodeV (v', EmptyV) -> v'::[]
    | NodeV (v',s') ->  v'::(converti_lista s');;

let rec remove_duplicate e = match e with 
                                | Of(t, lis) -> 
                                    let rec aux a = match a with
                                        | Lis(e_list) -> match e_list with
                                            | [] as l -> l
                                            | hd :: tl -> if (contain hd tl) then (aux (Lis(tl)))
                                                else hd :: (aux (Lis(tl)))
                                                    in let x = (Lis(aux(lis))) in Of(t, x)
                                | _ -> e;;

    
let rec ieval (e: expr) (env: evT env) : evT = 
    match e with
    | CstInt n -> Int n
    | CstBool b -> Bool b
    | CstString s -> String s
    | EqualsString (s, z) -> string_equals (ieval s env) (ieval z env)
    | Den i -> lookup env i 
    | Add (e1, e2) -> int_add (ieval e1 env) (ieval e2 env)
    | Sub (e1, e2) -> int_sub (ieval e1 env) (ieval e2 env) 
    | Times (e1, e2) -> int_times (ieval e1 env) (ieval e2 env) 
    | Mindi (e1, e2) -> int_mindi (ieval e1 env) (ieval e2 env)
    | IsZero e -> is_zero (ieval e env)
    | Equals (e1, e2) -> int_equals (ieval e1 env) (ieval e2 env) 
    | And (e1, e2) -> bool_and (ieval e1 env) (ieval e2 env) 
    | Or (e1, e2) -> bool_or (ieval e1 env) (ieval e2 env) 
    | Not e -> bool_not (ieval e env) 
    | IfThenElse (guardia, e1, e2) -> 
                                    ( 
                                        let guard_val = ieval guardia env in 
                                            match typecheck "bool" guard_val, guard_val with 
                                            | true, Bool true -> ieval e1 env 
                                            | true, Bool false -> ieval e2 env 
                                            | _,_ -> raise (DynamicTypeError "La guardia dell' ifthenelse deve essere di tipo booleano") 
                                    )
    | Let (i, e1, e2) -> let i_val = ieval e1 env in 
                            let env_1 = bind env i i_val in
                                                    ieval e2 env_1
                                    
    | Fun (i, t1, t2, body) -> Closure (i, t1, t2, body, env) 
    | FunR (funIde, p, t1, t2, bodyFun) -> RecClosure (funIde, p, t1, t2, bodyFun, env)
    | LetRec (funIde, p, t1, t2, bodyFun, bodyLet) -> let recClosure = ieval (FunR(funIde, p, t1, t2, bodyFun)) env in 
                                                    let bindEnv = bind env funIde recClosure in 
                                                        ieval bodyLet bindEnv 
    | Call (funct, arg) -> 
                            let funClosure = ieval funct env in 
                            (match funClosure with 
                            | Closure (param, t1, t2, bodyFun, declEnvFun) -> 
                                let actualVal = ieval arg env in 
                                if check_from_lang_tval t1 actualVal = true 
                                then (
                                        let actualEnv = bind declEnvFun param actualVal in 
                                            let return_value = (ieval bodyFun actualEnv) in if check_from_lang_tval t2 return_value = true then return_value 
                                                else  raise (DynamicTypeError "Call: ha fallito perchè il tipo valore ritornato dalla funzione  è errato")
                                )
                                else raise (DynamicTypeError "Call: ha fallito perchè il tipo del parametro attuale è errato")
                            | RecClosure (idFun, param, t1, t2, bodyFun, declEnvFun) -> 
                                let actualVal = ieval arg env in 
                                if check_from_lang_tval t1 actualVal = true 
                                then (
                                        let recEnv = bind declEnvFun idFun funClosure in 
                                        let actualEnv = bind recEnv param actualVal in 
                                         let return_value = (ieval bodyFun actualEnv) in if check_from_lang_tval t2 return_value = true then return_value 
                                                else  raise (DynamicTypeError "Call: ha fallito perchè il tipo valore ritornato dalla funzione  è errato")
                                )
                                else raise (DynamicTypeError "Call: ha fallito perchè il tipo del parametro attuale è errato")
                            | _ -> raise (DynamicTypeError "Call: ha fallito perchè il primo argomento non è una funzione")
                            ) 

    | EmptySet t -> Set(EmptyV) 
    | Singleton(e, t) -> 
                            let v = ieval e env in if check_from_lang_tval t v = true then 
                                (Set(NodeV(v,EmptyV))) else raise (DynamicTypeError "Singleton: tipo errato")
    | Of (t, e) -> let madeofset a = let rec aux b = 
                    match b with
                        | Lis(e_list) -> match e_list with 
                            | [hd] -> let v1 = ieval hd env in if check_from_lang_tval t v1 = true then (NodeV(v1, EmptyV)) else
                                raise (DynamicTypeError "Of: tipo errato")
                            | h::tail -> let v = ieval h env in if check_from_lang_tval t v = true then (NodeV(v, aux (Lis(tail)) )) 
                                else raise (DynamicTypeError "Singleton: tipo errato")
                        | _ -> failwith("unexpected") in 
                            let x = (aux a) in Set(x) in madeofset(e)
    | Intersection (set_e1, set_e2) -> 
                        ( let s1 = ieval set_e1 env in
                            let s2 = ieval set_e2 env in
                            match typecheck "Set" s1, typecheck "Set" s2, s1, s2 with 
                            | true, true, Set(set_v1), Set(set_v2) ->
                                                                                Set(set_intersection set_v1 set_v2)
                            | _, _, _, _ -> raise(DynamicTypeError "I tipi degli insiemi che si vogliono intersecare non combaciano o non sono di tipo Set")                            
                        ) 
    | Difference (set_e1, set_e2) -> (* differenza di due insiemi *)
                        (let s1 = ieval set_e1 env in
                            let s2 = ieval set_e2 env in
                            match typecheck "Set" s1, typecheck "Set" s2, s1, s2 with
                            | true, true, Set(set_v1), Set(set_v2) -> 
                                                                                Set(set_difference set_v1 set_v2) 
                            | _, _, _, _ -> raise(DynamicTypeError "I tipi degli insiemi di cui si vuole la differenza non combaciano o non sono di tipo Set")                            
                        )
    | Insert (e, set_e1) -> 
                        ( let s1 = ieval set_e1 env in
                            match typecheck "Set" s1, s1 with 
                            | true, Set(set_v) -> 
                                if (set_contains set_v (ieval e env) ) then Set(set_v) 
                                    else let v = ieval e env in Set(NodeV(v, set_v)) 
                            | _, _ -> raise(DynamicTypeError "Insert: ha fallito perchè non è stata chiamata su un insieme")                            
                        ) 
    | Union (set_e1, set_e2) ->
                        (let s1 = ieval set_e1 env in
                            let s2 = ieval set_e2 env in
                            match typecheck "Set" s1, typecheck "Set" s2, s1, s2 with
                            | true, true, Set(set_v1), Set(set_v2) ->  
                                Set(set_union set_v1 set_v2) 
                            | _, _, _, _ -> raise(DynamicTypeError "Union: ha fallito perchè non è stata chiamata su un insieme")                         
                        ) 
    | Maxim (set_e1) -> 
                        (let s1 = ieval set_e1 env in
                            match typecheck "Set" s1, s1 with 
                            | true, Set(set_v1) -> ( match set_v1 with
                                | NodeV(Int _, s) -> maxim set_v1 
                                | EmptyV -> raise(DynamicTypeError(" Non posso calcolare il massimo perche' l'insieme e' vuoto"))
                                | _ -> raise(DynamicTypeError(" Non puoi eseguire questo tipo di operazione su valori diversi da Int")))
                            | _, _ -> raise(DynamicTypeError "Maxim: ha fallito perchè non è stata chiamata su un insieme")                         
                        ) 
    | Minim (set_e1) -> 
                        (let s1 = ieval set_e1 env in
                            match typecheck "Set" s1, s1 with 
                            | true, Set(set_v1) -> (match set_v1 with
                                | NodeV(Int _, s) -> minim set_v1 
                                | EmptyV -> raise(DynamicTypeError(" Non posso calcolare il minim perche' l'insieme e' vuoto"))
                                | _ -> raise(DynamicTypeError(" Non puoi eseguire questo tipo di operazione su valori diversi da Int")))
                            | _, _ -> raise(DynamicTypeError "Minim: ha fallito perchè non è stata chiamata su un insieme")                         
                        ) 
    | Remove (e, insie) -> 
                        (let s1 = ieval insie env in
                            match typecheck "Set" s1, s1 with 
                            | true, Set(set_v) -> 
                                                let v = ieval e env in                                                              
                                                    Set(set_remove set_v v) 
                            | _, _ -> raise(DynamicTypeError "Remove: ha fallito perchè non è stata chiamata su un insieme")                            
                        ) 
    | Contains (e, insie) -> 
                                (let s1 = ieval insie env in
                                    match typecheck "Set" s1, s1 with 
                                    | true, Set(set_v) -> 
                                                        let v = ieval e env in Bool (set_contains set_v v)
                                    | _, _ -> raise(DynamicTypeError "Contains: ha fallito perchè non è stata chiamata su un insieme")  
                                )


   | Exists (funct, insie) -> 
                        (let s1 = ieval insie env in
                            match typecheck "Set" s1, s1 with 
                            | true, Set(set_v) ->  let funClosure = ieval funct env in
                                (match funClosure with
                                    | Closure (p, t1, t2, funBody, declEnvFun) -> 
                                        let rec aux lis = (match lis with
                                                            | h::d -> if (check_from_lang_tval t1 h = true) then 
                                                                    let return_value = ieval funBody (bind declEnvFun p h) in 
                                                                        if (check_from_lang_tval t2 return_value = true) 
                                                                            then if (return_value = Bool(true)) then Bool(true) else aux d 
                                                                                else raise(DynamicTypeError "Exists: tipo del valore ritornato diverso da quello definito")
                                                                                    else raise(DynamicTypeError "Exists: tipo del valore in input diverso da quello accettato dalla funzione")
                                                            | [] -> Bool(false))
                                                                in let ev_list = converti_lista(set_v) in
                                                                    aux ev_list  
                                    | _ -> raise (DynamicTypeError "Exists: ha fallito perchè il primo argomento non è una funzione") 
                                    )
                            | _, _ -> raise(DynamicTypeError "Exists: ha fallito perchè non è stata chiamata su un insieme")                            
                                )
                        
    | For_all (funct, insie) ->                 
                        (let s1 = ieval insie env in
                            match typecheck "Set" s1, s1 with 
                            | true, Set(set_v) ->  let funClosure = ieval funct env in
                                (match funClosure with
                                    | Closure (p, t1, t2, funBody, declEnvFun) -> 
                                        let rec aux lis = match lis with
                                                            | h::d -> if (check_from_lang_tval t1 h = true) then 
                                                                let return_value = ieval funBody (bind declEnvFun p h) in
                                                                    if (check_from_lang_tval t2 return_value = true)
                                                                        then if (return_value = Bool(false)) then Bool(false) else aux d
                                                                            else raise(DynamicTypeError "For_all: tipo del valore ritornato diverso da quello definito")
                                                                                else raise(DynamicTypeError "For_all: tipo del valore in input diverso da quello accettato dalla funzione")
                                                            | [] -> Bool(true)
                                                                in let ev_list = converti_lista(set_v) in
                                                                    aux ev_list
                                    | _ -> raise (DynamicTypeError "For_all: ha fallito perchè il primo argomento non è una funzione"))
                            | _, _ -> raise(DynamicTypeError "For_all: ha fallito perchè non è stata chiamata su un insieme")  )

    | Filter (funct, insie) ->                         (let s1 = ieval insie env in
                            match typecheck "Set" s1, s1 with 
                            | true, Set(set_v) ->  let funClosure = ieval funct env in
                                (match funClosure with
                                    | Closure (p, t1, t2, funBody, declEnvFun) -> 
                                        let rec aux lis = match lis with
                                                            | h::d -> if (check_from_lang_tval t1 h = true) then
                                                                let return_value = ieval funBody (bind declEnvFun p h) in 
                                                                    if (check_from_lang_tval t2 return_value = true) 
                                                                        then if (return_value = Bool(true)) then (NodeV(h, aux d)) else aux d
                                                                            else raise(DynamicTypeError "Filter: tipo del valore ritornato diverso da quello definito")
                                                                                else raise(DynamicTypeError "Filter: tipo del valore in input diverso da quello accettato dalla funzione")
                                                            | [] -> EmptyV 
                                                                in let ev_list = converti_lista(set_v) in 
                                                                    let new_setval = (aux ev_list) in Set(new_setval)
                                    | RecClosure (idFun, p, t1, t2, funBody, declEnvFun) -> 
                                        let rec aux lis = match lis with
                                                            | h::d -> let recEnv = bind declEnvFun idFun funClosure in 
                                                                if (check_from_lang_tval t2 h = true) then
                                                                    let return_value = ieval funBody (bind recEnv p h) in 
                                                                        if (check_from_lang_tval t1 return_value = true) 
                                                                            then if (return_value = Bool(true)) then (NodeV(h, aux d)) else aux d
                                                                                else raise(DynamicTypeError "Exists: tipo del valore ritornato diverso da quello definito")
                                                                                    else raise(DynamicTypeError "Exists: tipo del valore in input diverso da quello accettato dalla funzione")
                                                            | [] -> EmptyV 
                                                                in let ev_list = converti_lista(set_v) in 
                                                                    let new_setval = (aux ev_list) in Set(new_setval)
                                    | _ -> raise (DynamicTypeError "Filter: ha fallito perchè il primo argomento non è una funzione"))
                            | _,_ -> raise(DynamicTypeError "Filter: ha fallito perchè non è stata chiamata su un insieme")                            
                                )
    | Map (funct, insie) ->  (let s1 = ieval insie env in
                            match typecheck "Set" s1, s1 with 
                            | true, Set(set_v) ->  let funClosure = ieval funct env in
                               (match funClosure with
                                    | Closure (p, t1, t2, funBody, declEnvFun) -> 
                                        let rec aux lis = match lis with
                                                            | h::d -> if (check_from_lang_tval t1 h = true) then
                                                                let return_value = ieval funBody (bind declEnvFun p h) in 
                                                                    if (check_from_lang_tval t2 return_value = true) 
                                                                        then NodeV(return_value, aux d)
                                                                            else raise(DynamicTypeError "Map: tipo del valore ritornato diverso da quello definito")
                                                                                else raise(DynamicTypeError "Map: tipo del valore in input diverso da quello accettato dalla funzione") 
                                                            | [] -> EmptyV
                                                                in let ev_list = converti_lista(set_v) in 
                                                                    let new_setval = (aux ev_list) in Set(new_setval)
                                    | RecClosure (idFun, p, t1, t2, funBody, declEnvFun) -> let rec aux lis = match lis with
                                                            | h::d -> if (check_from_lang_tval t2 h = true) then 
                                                                let recEnv = bind declEnvFun idFun funClosure in 
                                                                    let return_value = ieval funBody (bind recEnv p h) in 
                                                                        if (check_from_lang_tval t1 return_value = true) 
                                                                            then NodeV(return_value, aux d)
                                                                                else raise(DynamicTypeError "Exists: tipo del valore ritornato diverso da quello definito")
                                                                                    else raise(DynamicTypeError "Exists: tipo del valore in input diverso da quello accettato dalla funzione")
                                                            | [] -> EmptyV
                                                                in let ev_list = converti_lista(set_v) in 
                                                                    let new_setval = (aux ev_list) in Set(new_setval)
                                    | _ -> raise (DynamicTypeError "Map: ha fallito perchè il primo argomento non è una funzione"))
                            | _, _ -> raise(DynamicTypeError "Map: ha fallito perchè non è stata chiamata su un insieme")                            
                                )
    | IssetEmpty insie ->
                        (let s1 = ieval insie env in
                            match typecheck "Set" s1, s1 with 
                            | true, Set(set_v) -> 
                                                if set_v = EmptyV 
                                                then Bool true
                                                else Bool false
                            | _, _ -> raise(DynamicTypeError "Impossibile chiamare IssetEmpty su qualcosa diverso dall'insieme") )      
    | Issubset(set_e1, set_e2) -> 
                                (let s1 = ieval set_e1 env in
                                    let s2 = ieval set_e2 env in

                                    match typecheck "Set" s1, typecheck "Set" s2, s1, s2  with 
                                    |  true, true, Set(set_v1), Set(set_v2) ->  Bool (is_subset set_v1 set_v2)
                                    | _, _, _, _ -> raise(DynamicTypeError "Issubset: ha fallito perchè non è stata chiamata su un insieme")  
                                )               
                        ;;



let rec teval (p : expr) (tenv : tval env) : tval = match p with
    | CstBool b -> TBool
	| CstInt i -> TInt
    | CstString s -> TString
    | EqualsString (e1,e2) -> let t1 = teval e1 tenv in 
                                let t2 = teval e2 tenv in 
                                    (match (t1, t2) with 
                                        | (TString, TString) -> TBool 
                                        | (_,_)  -> raise (WrongType("WrongType in EqualsString")) )
    | Den s -> lookup tenv s 
    | Add (e1,e2) -> let t1 = teval e1 tenv in 
                                let t2 = teval e2 tenv in 
                                   (match (t1, t2) with
                                        | (TInt, TInt) -> TInt 
                                        | (_,_)  -> raise (WrongType("WrongType in Add"))  )
    | Sub (e1,e2) -> let t1 = teval e1 tenv in
                                let t2 = teval e2 tenv in 
                                   (match (t1, t2) with 
                                        | (TInt, TInt) -> TInt 
                                        | (_,_)  -> raise (WrongType("WrongType in Sub"))  )
    | Times (e1,e2) -> let t1 = teval e1 tenv in
                                let t2 = teval e2 tenv in 
                                    (match (t1, t2) with 
                                        | (TInt, TInt) -> TInt 
                                        | (_,_)  -> raise (WrongType("WrongType in Times"))  )
    | Mindi (e1,e2) -> let t1 = teval e1 tenv in 
                                let t2 = teval e2 tenv in 
                                    (match (t1, t2) with 
                                        | (TInt, TInt) -> TBool
                                        | (_,_)  -> raise (WrongType("WrongType in Mindi"))  )
    | IsZero e -> TInt
    | Equals (e1,e2) -> let t1 = teval e1 tenv in 
                                let t2 = teval e2 tenv in 
                                    (match (t1, t2) with 
                                        | (TInt, TInt) -> TBool 
                                        | (_,_)  -> raise (WrongType("WrongType in Equals")) )
    | And (e1,e2) -> let t1 = teval e1 tenv in 
                                let t2 = teval e2 tenv in 
                                    (match (t1, t2) with 
                                        | (TBool, TBool) -> TBool 
                                        | (_,_)  -> raise (WrongType("WrongType in And"))  )
    | Or (e1,e2) -> let t1 = teval e1 tenv in 
                                let t2 = teval e2 tenv in 
                                    (match (t1, t2) with 
                                        | (TBool, TBool) -> TBool 
                                        | (_,_)  -> raise (WrongType("WrongType in Or"))  )
    | Not e -> TBool (* uguale a sopra *)
    | IfThenElse (e,e1,e2) -> let t = teval e tenv in 
                                 (match t with 
                                    | TBool -> let t1 = teval e1 tenv in let t2 = teval e2 tenv in 
                                        ( match (t1, t2) with 
                                            | (TInt, TInt) -> TInt 
                                            | (TBool, TBool) -> TBool 
                                            | (TString, TString) -> TString
                                            | (_,_) -> raise (WrongType("WrongType in IfThenElse (I due rami non hanno lo stesso tipo o sono funzioni (non accettate) o sono Set(non accettati))"))  ) 
                                    | _ -> raise (WrongType("WrongType in IfThenElse (la guardia non e' un booleano)"))  )
    | Let(x, e1, e2) -> let t = teval e1 tenv in 
                                    teval e2 (bind tenv x t)
    | Fun(x, t1, t2, e) ->  let tenv1 = bind tenv x t1 in  
                                let t_fun = teval e tenv1 in if (t_fun = t2)
                                    then FunT(t1,t_fun)                        
                                        else raise (WrongType("Il tipo del parametro fornito alla Call nel Fun non e' corretto"))
    | FunR(x, p, t1, t2, bodyFun) ->    let tenv1 = bind tenv p t2 in
                                            let tenv2 = bind tenv1 x (FunT(t2, t1)) in
                                                let t_fun = teval bodyFun tenv2 in if (t_fun = t1)
                                                    then FunT(t2, t_fun)
                                                        else raise (WrongType("Il tipo del parametro fornito alla Call nel FunR non e' corretto"))

    | LetRec (x, p, t1, t2, bodyFun, bodyLet) -> let tenv1 = bind tenv p t2 in
                                                    let tenv2 = bind tenv1 x (FunT(t2, t1)) in
                                                        let t_fun = teval bodyFun tenv2 in  if (t_fun = t1 && (teval bodyLet tenv2) = t2) 
                                                            then FunT(t2, t_fun) 
                                                                else raise (WrongType("Il tipo del parametro fornito alla Call nel Letrec non e' corretto"))
    | Call(e1, e2) -> let f = teval e1 tenv in 
                                 (match f with 
                                    | FunT(t1,t2) -> if ((teval e2 tenv) = t1) then t2 else raise (WrongType "WrongType in Call (secondo parametro ha un tipo non corretto)")
                                    | _ -> raise (WrongType("WrongType in Call (il primo parametro non e' una funzione)"))  )
    | EmptySet t -> SetT(t)
    | Singleton(e, t) -> let t1 = teval e tenv in if (t1 = t) then SetT(t) else raise (WrongType("WrongType in Set (il tipo fornito a Singleton e' diverso da quello della espressione fornita)"))
    | Of (t, e) -> let madeofset a = let rec aux b = ( match b with
                        | Lis(e_list) -> match e_list with 
                            | [hd] -> let t1 = teval hd tenv in if (t1 = t) then hd
                                else raise (WrongType("WrongType in Of (l'ultimo parametro ha un tipo differente da quello fornito)"))
                            | h::tail -> let t2 = teval h tenv in if (t2 = t) then aux (Lis(tail)) 
                                else raise (WrongType("WrongType in Of (alcune espressione hanno tipo differente da quello fornito)")) 
                        | _ -> failwith("Of accetta espressioni solo nella forma Lis(exp_list)") ) in 
                            let inutile = (aux a) in SetT(t) in madeofset(e)
    | Intersection(s1, s2) ->let t1 = teval s1 tenv in 
                                    let t2 = teval s2 tenv in
                                        if t1 = t2 then SetT(t1) 
                                            else raise (WrongType("WrongType in Intersection (non e' stato passato un tipo Set)"))
                                            
    | Difference(s1, s2) ->let t1 = teval s1 tenv in 
                                    let t2 = teval s2 tenv in
                                        if t1 = t2 then SetT(t1) 
                                            else raise (WrongType("WrongType in Difference (non e' stato passato un tipo Set)"))
    | Union(s1, s2) ->let t1 = teval s1 tenv in 
                                    let t2 = teval s2 tenv in
                                        if t1 = t2 then SetT(t1) 
                                            else raise (WrongType("WrongType in Union (non e' stato passato un tipo Set)"))
    | Insert(e, insie) -> let t1 = teval e tenv in 
                                    let t2 = teval insie tenv in
                                        ( match t2 with
                                            | SetT(t) -> if t = t1 then SetT(t)
                                                else raise (WrongType("WrongType in Insert (stai cercando di inserire in un'insieme un elemento di tipo diverso da quello dell'insieme)"))
                                            | _ -> raise (WrongType("WrongType in Insert (stai cercando di inserire un elemento in qualcosa che non e' un'insieme)"))
                                            )          
    | Remove(e, insie) -> let t1 = teval e tenv in 
                                    let t2 = teval insie tenv in
                                        ( match t2 with
                                            | SetT(t) -> if t = t1 then SetT(t)
                                                else raise (WrongType("WrongType in Remove (stai cercando di rimuovere un elemento di tipo diverso da quello dell'insieme)"))
                                            | _ -> raise (WrongType("WrongType in Remove (stai cercando di rimuovere un elemento da qualcosa che non e' un'insieme)"))
                                            )    
    | Contains(e, insie) -> let t1 = teval e tenv in 
                                    let t2 = teval insie tenv in
                                        ( match t2 with
                                            | SetT(t) -> if t = t1 then SetT(t)
                                                else raise (WrongType("WrongType in Insert (questo elemento non appartiene all'insieme perche' di tipo diverso dall'insieme)"))
                                            | _ -> raise (WrongType("WrongType in Insert (stai cercando un elemento in qualcosa che non e' un'insieme)"))
                                            )   
    | IssetEmpty(insie) -> let t1 = teval insie tenv in 
                                        ( match t1 with
                                            | SetT(t) -> SetT(t)
                                            | _ -> raise (WrongType("WrongType in IssetEmpty (quello passato non e' un'insieme)"))
                                            )          
    | Maxim(insie) -> let t1 = teval insie tenv in 
                                        ( match t1 with
                                            | SetT(t) -> SetT(t)
                                            | _ -> raise (WrongType("WrongType in Maxim (quello passato non e' un'insieme)"))
                                            )    
    | Minim(insie) -> let t1 = teval insie tenv in 
                                        ( match t1 with
                                            | SetT(t) -> SetT(t)
                                            | _ -> raise (WrongType("WrongType in Minim (quello passato non e' un'insieme)"))
                                            )         
    | Issubset (s1, s2) ->  let t1 = teval s1 tenv in
                                        let t2 = teval s2 tenv in
                                            if t1 = t2 then TBool
                                                else raise (WrongType("WrongType in Intersection (non e' stato passato un tipo Set)"))
    | Exists (funct, insie) -> let t1 = teval funct tenv in 
                                    let t2 = teval insie tenv in
                                        ( match (t1, t2) with
                                            | (FunT(TInt, TBool), SetT(t2)) -> TBool 
                                            | (_, _) -> raise (WrongType("WrongType in Exists "))
                                            )
    | For_all (funct, insie) -> let t1 = teval funct tenv in 
                                    let t2 = teval insie tenv in
                                        ( match (t1, t2) with
                                            | (FunT(TInt, TBool), SetT(t2)) -> TBool 
                                            | (_, _) -> raise (WrongType("WrongType in For_all "))
                                            )
    | Filter (funct, insie) -> let t1 = teval funct tenv in 
                                    let t2 = teval insie tenv in
                                        ( match (t1, t2) with
                                            | (FunT(TInt, TBool), SetT(t2)) -> SetT(t2) 
                                            | (_, _) -> raise (WrongType("WrongType in Filter "))
                                            )
    | Map (funct, insie) ->   let t1 = teval funct tenv in 
                                    let t2 = teval insie tenv in
                                        ( match (t1, t2) with
                                            | (FunT(TInt, TInt), SetT(t2)) -> SetT(t2) 
                                            | (_, _) -> raise (WrongType("WrongType in Map "))
                                            )
                            ;;

let eval (e : expr) (env : evT env) : evT = let deduplicat_e = (remove_duplicate e) in 
    let xtyp = teval deduplicat_e [] in
        let xval = ieval deduplicat_e env in xval;;



(*  TESTS  *)
(* MAP-EXISTS-FORALL-FILTER *)
let test_map : expr = Map(FunR("fact", "n", TInt, TInt,
IfThenElse(Equals(Den("n"),CstInt(0)),CstInt(1),Times(Den("n"),Call(Den("fact"),Sub(Den("n"),CstInt(1)))))), 
Of(TInt, Lis[(CstInt(1)); CstInt(2); CstInt(3); CstInt(4)]));;

(* Use of EXISTS*)
let test_exists : expr = Exists(Fun("x", TInt, TBool, IfThenElse(Equals(Den "x", CstInt 1), CstBool true, CstBool false)), Of(TInt, Lis([CstInt 3; CstInt 4; CstInt 1])));;

(* Use of FORALL *)
let test_for_all : expr = For_all(Fun("x", TInt, TBool, IfThenElse(Mindi(Den "x", CstInt 0), CstBool true, CstBool false)), Of(TInt, Lis([CstInt(-333); CstInt (-4); CstInt(-333); CstInt (-30); CstInt(-2); CstInt(-3)])));;

(* Use of FILTER*)
let test_filter : expr = Filter(Fun("x", TInt, TBool, IfThenElse(Mindi(CstInt(22), Den "x"), CstBool true, CstBool false)), Of(TInt, Lis([CstInt 23; CstInt 4; CstInt(-1); CstInt 43; CstInt(-2); CstInt 123])));;

(* Use of INSERT e EMPTYSET*)
let test_insert : expr = Insert(CstString("nuova_stringa"), EmptySet(TString));;

(* Use of ISSEMPTY e REMOVE*)
let test_remove_issempty : expr = IssetEmpty(Remove(CstString("stringa_rimossa"), Singleton(CstString("stringa_rimossa"), TString)));;

(* Use of MINIM-MAXIM*)
let test_minim : expr = Minim(Of(TInt, Lis[(CstInt(3)); CstInt(-22); CstInt(-99) ; CstInt(-2)]));;
let test_maxim : expr = Maxim(Of(TInt, Lis[(CstInt(3)); CstInt(-22); CstInt(-99) ; CstInt(22)]));;

(* Use of CONTAINS*)
let test_contains : expr = Contains(CstInt(20), Of(TInt, Lis[(CstInt(2)); CstInt(20); CstInt(-33)]));;

(* Use of UNION*)
let test_union : expr = Union(Singleton(CstInt(-332), TInt), Of(TInt, Lis[(CstInt(2)); CstInt(3); CstInt(-33)]));;

(* Use of INTERSECTION*)
let test_intersection : expr = Intersection(Singleton(CstInt(-33), TInt), Of(TInt, Lis[(CstInt(2)); CstInt(3); CstInt(-33)]));;

(* Use of Difference*)
let test_difference : expr = Difference(Singleton(CstInt(-33), TInt), Of(TInt, Lis[(CstInt(2)); CstInt(3); CstInt(-33); CstInt(99)]));;

(* Use of LetRec*)
let test_letrec : expr = LetRec("fact", "n", TInt, TInt,
IfThenElse(Equals(Den("n"),CstInt(0)),CstInt(1),Times(Den("n"),Call(Den("fact"),Sub(Den("n"),CstInt(1))))), 
Call(Den "fact", CstInt(3)) );;

let test_issubset : expr = Issubset(Of(TInt, Lis([CstInt(-33); CstInt(2)])), Of(TInt, Lis[(CstInt(2)); CstInt(3); CstInt(-33); CstInt(99)]));;

eval test_map [];;
