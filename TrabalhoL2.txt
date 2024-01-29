   (* ========================================= *)
   (*    Sintaxe Abstrata                       *)
   (* ========================================= *)

(*  T ::= int | bool | T1 --> T2 |  T1 * T2  *)

type tipo = 
    TyInt 
  | TyBool
  | TyFn of tipo * tipo
  | TyPair of tipo * tipo 
  | TyRef of tipo
  | TyUnit
              
type ident = string
  
type bop = Sum | Sub | Mult  | Gt | Lt | Geq | Leq | Eq
  
   
   (* e ::= n | x | b | e1 op e2 
          | (e1,e2) | fst e | snd e
          | if e1 then e2 else e3
          | fn x:T => e | e1 e2 | let x:T = e1 in e2
          | let rec f: T1--> T2 = fn x: T1 => e1 in e2 *)
    
type expr  = 
    Num of int  
  | Var of ident 
  | True
  | False
  | Binop of bop * expr * expr
  | Pair of expr * expr 
  | Fst of expr
  | Snd of expr 
  | If of expr * expr * expr
  | Fn of ident * tipo * expr  
  | App of expr * expr
  | Let of ident * tipo * expr * expr
  | LetRec of ident * tipo * expr  * expr
  | Asg of expr * expr
  | Dref of expr 
  | New of expr
  | Seq of expr * expr
  | Whl of expr * expr 
  | Skip 
    
type tenv = (ident * tipo) list 

type valor = 
    VNum of int
  | VTrue 
  | VFalse
  | VPair of valor * valor
  | VClos of ident * expr * renv
  | VRclos of ident * ident * expr * renv
and 
  renv = (ident * valor) list
    
    (* funções polimórficas para ambientes *)
    
let rec lookup a k  = 
  match a with
    [] -> None
  | (y,i) :: tl -> if (y = k) then Some i else lookup tl k
  
let rec update a k i = 
  (k,i) :: a
  
    (* exceções que não devem ocorrer *)

exception BugParser
  
exception BugTypeInfer

  
   (* ========================================= *)
   (*    TypeInfer                              *)
   (* ========================================= *) 


(* TypeError é ativada se programador L1 escreveu expressão mal tipada *)  
exception TypeError of string 
    
    
    
let rec typeinfer (gamma: tenv) (e:expr) : tipo  = 
  match e with
  
    (* TInt *)
  | Num _ -> TyInt 
    
    (* TVar *)
  | Var x -> 
      (match lookup gamma x with
         Some t -> t
       | None   -> raise (TypeError ("variavel nao declarada:" ^ x))) 
                                                                      
    (* TBool *)
  | True  -> TyBool
  | False -> TyBool 
  
    (*  G |-- e1:int    G |-- e2:int     bop in {+,-,*}
       ------------------------------------------------
                 G |-- e1  bop  e2 : int 
                 
       G |-- e1:int    G |-- e2:int     bop in {=, <, >, >=, <=,*}
       ----------------------------------------------------------
                 G |-- e1  bop  e2 : bool
                
*) 
    
  | Binop(oper,e1,e2) -> 
      let t1 = typeinfer gamma e1 in
      let t2 = typeinfer gamma e2 in
      if t1 = TyInt && t2 = TyInt then 
        (match oper with
           Sum | Sub | Mult -> TyInt
         | Eq | Lt | Gt | Geq | Leq -> TyBool) 
      else raise (TypeError "operando nao é do tipo int")
  
  (* TPair *)    
  | Pair(e1,e2) -> TyPair(typeinfer gamma e1, typeinfer gamma e2) 
  
  (* TFst *)
  | Fst e1 -> 
      (match typeinfer gamma e1 with
         TyPair(t1,_) -> t1
       | _ -> raise (TypeError "fst espera tipo par"))
  
  (* TSnd *)
  | Snd e1 -> 
      (match typeinfer gamma e1 with
         TyPair(_,t2) -> t2
       | _ -> raise (TypeError "snd espera tipo par")) 
                                                       
  (* TIf *)
  | If(e1,e2,e3) -> 
      ( match typeinfer gamma e1 with 
          TyBool -> 
            let t2 = typeinfer gamma e2 in
            let t3 = typeinfer gamma e3
            in if t2 = t3 then t2 
            else raise (TypeError "then e else com tipos diferentes")
        | _ -> raise (TypeError "condição de IF não é do tipo bool")) 
  
  (* TFn *)
  | Fn(x,t,e1) -> 
      let t1 = typeinfer (update gamma x t) e1
      in TyFn(t,t1)
  
  (* TApp *)
  | App(e1,e2) -> 
      (match typeinfer gamma e1 with
         TyFn(t, t') ->  if (typeinfer gamma e2) = t then t' 
           else raise (TypeError "tipo argumento errado" )
       | _ -> raise (TypeError "tipo função era esperado"))
  
  (* TLet *)
  | Let(x,t,e1,e2) -> 
      if (typeinfer gamma e1) = t then typeinfer (update gamma x t) e2
      else raise (TypeError "expr nao é do tipo declarado em Let" )
  
          
  | LetRec(f,(TyFn(t1,t2) as tf), Fn(x,tx,e1), e2) -> 
      let gamma_tf = update gamma f tf in
      let gamma_tf_tx = update gamma_tf x tx in
      if (typeinfer gamma_tf_tx e1) = t2 then typeinfer gamma_tf e2
      else raise (TypeError "tipo da funcao diferente do tipo declarado" )
  
   (* se não colocarmos essa ultimo pattern teremos warning:
      pattern matching non exhaustive *)  

  | LetRec _ -> raise BugParser 
                  
                  
  
   (* ========================================= *)
   (*    Avaliador                              *)
   (* ========================================= *)

(* função auxiliar que computa as operações binárias *) 

let compute (oper: bop) (v1: valor) (v2:valor) : valor = 
  match (oper,v1,v2) with
    (Sum, VNum(n1),  VNum(n2)) -> VNum (n1 + n2) 
  | (Sub, VNum(n1),  VNum(n2)) -> VNum (n1 - n2)
  | (Mult, VNum(n1), VNum(n2)) -> VNum (n1 * n2)
  | (Eq, VNum(n1), VNum(n2))  -> if (n1 = n2) then VTrue else VFalse
  | (Gt, VNum(n1), VNum(n2))  -> if (n1 > n2) then VTrue else VFalse
  | (Lt, VNum(n1), VNum(n2))  -> if (n1 < n2) then VTrue else VFalse
  | (Geq, VNum(n1), VNum(n2)) -> if (n1 >= n2) then VTrue else VFalse
  | (Leq, VNum(n1), VNum(n2)) -> if (n1 <= n2) then VTrue else VFalse
  | _ -> raise BugTypeInfer

(* regras da semântic operacional big step com ambientes *)
let rec eval (renv:renv) (e:expr) : valor = 
  match e with 
    Num n -> VNum n
  | True -> VTrue 
  | False -> VFalse
    
  | Var x -> 
      (match lookup renv x with
         Some v -> v 
       | None -> raise BugTypeInfer) 
      
  | Binop(oper,e1,e2) -> 
      let v1 = eval renv e1 in 
      let v2 = eval renv e2  
      in compute oper v1 v2

  | Pair(e1,e2) -> 
      let v1 = eval renv e1 in 
      let v2 = eval renv e2 
      in VPair(v1, v2)
        
  | Fst e -> 
      (match eval renv e with
         VPair(v1,_) -> v1
       | _ -> raise BugTypeInfer) 
      
  | Snd e -> 
      (match eval renv e with
         VPair(_,v2) -> v2
       | _ -> raise BugTypeInfer)
      
  | If(e1,e2,e3) -> 
      (match eval renv e1 with 
         VTrue -> eval renv e2 
       | VFalse -> eval renv e3
       | _ -> raise BugTypeInfer)
      
  | Fn(x,_,e1) -> VClos(x,e1,renv)
  
  | App(e1,e2) ->
      let v1 = eval renv e1 in
      let v2 = eval renv e2 in
      (match v1 with
         VClos(x,ebdy,renv') -> 
           let renv'' = update renv' x v2
           in eval renv'' ebdy
             
       | VRclos(f,x,ebdy,renv') ->
           let renv'' = update renv' x v2 in
           let renv''' = update renv'' f v1
           in eval renv''' ebdy
             
       | _ -> raise BugTypeInfer)
      
  | Let(x,_,e1,e2) -> 
      let v1 = eval renv e1 
      in eval (update renv x v1) e2
        
  | LetRec(f,TyFn(t1,t2),Fn(x,tx,e1), e2) when t1 = tx ->
      let renv' = update renv f (VRclos(f,x,e1,renv))
      in eval renv' e2
        
  | LetRec _ -> raise BugParser 
  

  (* função auxiliar que converte tipo para string *)    

let rec ttos (t:tipo) : string = 
  match t with 
    TyInt -> "int"
  | TyBool -> "bool"
  | TyFn(t1,t2)   -> "(" ^ (ttos t1) ^ "-->" ^ (ttos t2) ^ ")"
  | TyPair(t1,t2) -> "(" ^ (ttos t1) ^ " * " ^ (ttos t2) ^ ")"

 
  (* função auxiliar que converte valor para string *)     

let rec vtos (v: valor) : string = 
  match v with
    VNum n -> string_of_int n
  | VTrue -> "true"
  | VFalse -> "false"
  | VPair(v1,v2) ->
      "(" ^ (vtos v1) ^ "," ^ (vtos v2) ^ ")"
  | VClos _ -> "fn"
  | VRclos _ -> "fn" 
            
   
   (* ========================================= *)
   (*    Interpretador                          *)
   (* ========================================= *)
         
let int_bse (e:expr)  = 
  try
    let t = typeinfer [] e in
    let v = eval [] e   
    in  print_string ((vtos v) ^ " : " ^ (ttos t))
  with 
    TypeError msg -> print_string ("erro de tipo: " ^ msg)
  
   (* as exceções abaixo não podem ocorrer *) 
  | BugTypeInfer  -> print_string "corrigir bug no typeinfer"
  | BugParser     -> print_string "corrigir bug do parser para let rec" 
  
  