section\<open>Environment and State\<close>
theory Environment
imports Accounts Storage StateMonad
begin

(*
  Fixme: Change all datatypes to lower-case
*)

subsection \<open>Environment\<close>

datatype Type = Value Types
              | Calldata MTypes
              | Memory MTypes
              | Storage STypes
 
datatype Denvalue = Stackloc Location
                  | Storeloc Location

record Environment =
  address :: Address (*address of executing contract*)
  contract :: Identifier
  sender :: Address (*address of calling contract*)
  svalue :: Valuetype (*money send*)
  denvalue :: "(Identifier, Type \<times> Denvalue) fmap"
 
fun identifiers :: "Environment \<Rightarrow> Identifier fset"
  where "identifiers e = fmdom (denvalue e)"
 
definition emptyEnv :: "Address \<Rightarrow> Identifier \<Rightarrow> Address \<Rightarrow> Valuetype \<Rightarrow> Environment"
  where "emptyEnv a c s v = \<lparr>address = a, contract = c, sender = s, svalue = v, denvalue = fmempty\<rparr>"

declare emptyEnv_def [solidity_symbex]

lemma emptyEnv_address[simp]:
  "address (emptyEnv a c s v) = a"
  unfolding emptyEnv_def by simp

lemma emptyEnv_members[simp]:
  "contract (emptyEnv a c s v) = c"
  unfolding emptyEnv_def by simp

lemma emptyEnv_sender[simp]:
  "sender (emptyEnv a c s v) = s"
  unfolding emptyEnv_def by simp

lemma emptyEnv_svalue[simp]:
  "svalue (emptyEnv a c s v) = v"
  unfolding emptyEnv_def by simp

lemma emptyEnv_denvalue[simp]:
  "denvalue (emptyEnv a c s v) = {$$}"
  unfolding emptyEnv_def by simp

definition eempty :: "Environment"
  where "eempty = emptyEnv (STR '''') (STR '''') (STR '''') (STR '''')"

declare eempty_def [solidity_symbex]

fun updateEnv :: "Identifier \<Rightarrow> Type \<Rightarrow> Denvalue \<Rightarrow> Environment \<Rightarrow> Environment"
  where "updateEnv i t v e = e \<lparr> denvalue := fmupd i (t,v) (denvalue e) \<rparr>"

fun updateEnvOption :: "Identifier \<Rightarrow> Type \<Rightarrow> Denvalue \<Rightarrow> Environment \<Rightarrow> Environment option"
  where "updateEnvOption i t v e = (case fmlookup (denvalue e) i of 
              Some _ \<Rightarrow> None
            | None \<Rightarrow> Some (updateEnv i t v e))"

lemma updateEnvOption_address: "updateEnvOption i t v e = Some e' \<Longrightarrow> address e = address e'"
by (auto split:option.split_asm)

fun updateEnvDup :: "Identifier \<Rightarrow> Type \<Rightarrow> Denvalue \<Rightarrow> Environment \<Rightarrow> Environment"
  where "updateEnvDup i t v e = (case fmlookup (denvalue e) i of 
              Some _ \<Rightarrow> e
            | None \<Rightarrow> updateEnv i t v e)"

lemma updateEnvDup_address[simp]: "address (updateEnvDup i t v e) = address e"
  by (auto split:option.split)

lemma updateEnvDup_sender[simp]: "sender (updateEnvDup i t v e) = sender e"
  by (auto split:option.split)

lemma updateEnvDup_svalue[simp]: "svalue (updateEnvDup i t v e) = svalue e"
  by (auto split:option.split)

lemma updateEnvDup_contract[simp]: "contract (updateEnvDup i t v e) = contract e"
  by (auto split:option.split)

lemma updateEnv_den_sub: "fmdom (denvalue e) |\<subseteq>| fmdom(denvalue (updateEnv i t v e))" by auto 


lemma updateEnvDup_dup:
  assumes "i\<noteq>i'" shows "fmlookup (denvalue (updateEnvDup i t v e)) i' = fmlookup (denvalue e) i'"
proof (cases "fmlookup (denvalue e) i = None")
  case True
  then show ?thesis using assms by simp
next
  case False
  then obtain e' where "fmlookup (denvalue e) i = Some e'" by auto
  then show ?thesis using assms by simp
qed

lemma env_reorder_neq:
  assumes "x\<noteq>y"
  shows "updateEnv x t1 v1 (updateEnv y t2 v2 e) = updateEnv y t2 v2 (updateEnv x t1 v1 e)"
proof -
  have "address (updateEnv x t1 v1 (updateEnv y t2 v2 e)) = address (updateEnv y t2 v2 (updateEnv x t1 v1 e))" by simp
  moreover from assms have "denvalue (updateEnv x t1 v1 (updateEnv y t2 v2 e)) = denvalue (updateEnv y t2 v2 (updateEnv x t1 v1 e))" using Finite_Map.fmupd_reorder_neq[of x y "(t1,v1)" "(t2,v2)"] by simp
  ultimately show ?thesis by simp
qed

lemma uEO_in:
  assumes "i |\<in>| fmdom (denvalue e)"
  shows "updateEnvOption i t v e = None"
  using assms by auto

lemma uEO_n_In:
  assumes "\<not> i |\<in>| fmdom (denvalue e)"
  shows "updateEnvOption i t v e = Some (updateEnv i t v e)"
  using assms by auto

fun astack :: "Identifier \<Rightarrow> Type \<Rightarrow> Stackvalue \<Rightarrow> Stack * Environment \<Rightarrow> Stack * Environment"
  where "astack i t v (s, e) = (push v s, (updateEnv i t (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc s))) e))"

fun astack_dup :: "Identifier \<Rightarrow> Type \<Rightarrow> Stackvalue \<Rightarrow> Stack * Environment \<Rightarrow> Stack * Environment"
  where "astack_dup i t v (s, e) = 
                                    (case fmlookup (denvalue e) i of 
                                          Some _ \<Rightarrow> (s, e)
                                        | None \<Rightarrow> (push v s, updateEnv i t (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc s))) e))
"
lemma astack_dup_is_astack:
  assumes "denvalue e $$ i = None"
  shows "astack i t v (s, e) = astack_dup i t v (s, e)" using assms by simp

lemma astack_den_sub:"fmdom (denvalue e) |\<subseteq>| fmdom(denvalue (snd (astack i t v (s, e))))" using updateEnv_den_sub by auto
lemma astack_dup_den_sub:"fmdom (denvalue e) |\<subseteq>| fmdom(denvalue (snd (astack_dup i t v (s, e))))" 
  unfolding astack_dup.simps using updateEnv_den_sub by (auto split:option.splits)
lemma astack_dup_env:
  assumes "astack_dup i t v (s,e) = (sk, env)"
  shows "address e = address env \<and> contract e = contract env \<and> sender e = sender env \<and> svalue e = svalue env"
proof(cases "fmlookup (denvalue e) i")
  case None
  then show ?thesis using assms(1) by auto
next
  case (Some a)
  then show ?thesis using assms(1) by auto
qed

lemma astack_dup_denvalue:
  assumes "astack_dup i t v (s,e) = (sk, env)"
  shows "denvalue e $$ i = Some y \<longrightarrow> denvalue env $$ i = Some y"
  using assms 
  by (metis Option.option.simps(5) astack_dup.simps snd_conv updateEnvDup.simps)

subsubsection \<open>Examples\<close>
abbreviation "myenv::Environment \<equiv> eempty \<lparr>denvalue := fmupd STR ''id1'' (Value TBool, Stackloc STR ''0'') fmempty\<rparr>"
abbreviation "mystack::Stack \<equiv> \<lparr>mapping = fmupd (STR ''0'') (KValue STR ''True'') fmempty, toploc = 1\<rparr>"

abbreviation "myenv2::Environment \<equiv> eempty \<lparr>denvalue := fmupd STR ''id2'' (Value TBool, Stackloc STR ''1'') (fmupd STR ''id1'' (Value TBool, Stackloc STR ''0'') fmempty)\<rparr>"
abbreviation "mystack2::Stack \<equiv> \<lparr>mapping = fmupd (STR ''1'') (KValue STR ''False'') (fmupd (STR ''0'') (KValue STR ''True'') fmempty), toploc = 2\<rparr>"

lemma "astack (STR ''id1'') (Value TBool) (KValue (STR ''True'')) (emptyStore, eempty) = (mystack,myenv)" by solidity_symbex
lemma "astack (STR ''id2'') (Value TBool) (KValue (STR ''False'')) (mystack, myenv) = (mystack2,myenv2)" by solidity_symbex

subsection \<open>Declarations\<close>

text \<open>This function is used to declare a new variable: decl id tp val copy cd mem sto c m k e
\begin{description}
  \item[id] is the name of the variable
  \item[tp] is the type of the variable
  \item[val] is an optional initialization parameter. If it is None, the types default value is taken.
  \item[copy] is a flag to indicate whether memory should be copied (from mem parameter) or not (copying is required for example for external method calls).
  \item[cd] is the original calldata which is used as a source
  \item[mem] is the original memory which is used as a source
  \item[sto] is the original storage which is used as a source
  \item[c] is the new calldata which is updated
  \item[m] is the new memory which is updated
  \item[k] is the new calldata which is updated
  \item[e] is the new environment which is updated
\end{description}\<close>
fun decl :: "Identifier \<Rightarrow> Type \<Rightarrow> (Stackvalue * Type) option \<Rightarrow> bool \<Rightarrow> CalldataT \<Rightarrow> MemoryT \<Rightarrow> (StorageT)
    \<Rightarrow> CalldataT \<times> MemoryT \<times> Stack \<times> Environment \<Rightarrow> (CalldataT \<times> MemoryT \<times> Stack \<times> Environment) option"
  where
(* Declaring stack variables *)
  "decl i (Value t) None _ _ _ _ (c, m, k, e) = 
    
        Some (c, m, (astack_dup i (Value t) (KValue (ival t)) (k, e))) 
      "
| "decl i (Value t) (Some (KValue v, Value t')) _ _ _ _ (c, m, k, e) =
   Option.bind (convert t' t v)
    (\<lambda>v'. Some (c, m, astack_dup i (Value t) (KValue v') (k, e)))"
| "decl _ (Value _) _ _ _ _ _ _ = None"

(* Declaring calldata variables *)
| "decl i (Calldata (MTArray x t)) (Some (KCDptr p, t')) True cd _ _ (c, m, k, e) =
  (if (t' = (Calldata (MTArray x t)) \<and> x > 0 \<and> denvalue e $$ i = None) then 
    (let l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc c);
         (_, c') = allocate c
     in Option.bind (cpm2m p l x t cd c')
      (\<lambda>c''. Some (c'', m, astack_dup i (Calldata (MTArray x t)) (KCDptr l) (k, e)))) else None)"
(*t' (the type which is being "copied" must be the same as the new variable but would be memory
  and not calldata. In other words when copying a memory structure to call data the struct must be the
  same but the actually type is not important *)
| "decl i (Calldata (MTArray x t)) (Some (KMemptr p, t')) True _ mem _ (c, m, k, e) =
  (if (t' = (Memory (MTArray x t)) \<and> x > 0 \<and> denvalue e $$ i = None) then 
    (let l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc c);
         (_, c') = allocate c
     in Option.bind (cpm2m p l x t mem c')
      (\<lambda>c''. Some (c'', m, astack_dup i (Calldata (MTArray x t)) (KCDptr l) (k, e)))) else None)"
| "decl i (Calldata _) _ _ _ _ _ _ = None"

(* Declaring memory variables *)
| "decl i (Memory (MTArray x t)) None _ _ _ _ (c, m, k, e) =
(if denvalue e $$ i = None \<and> arraysGreaterZero (MTArray x t) then
(let m' = minit x t m
      in Some (c, m', astack_dup i (Memory (MTArray x t)) (KMemptr (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m))) (k, e))
)else None)"
| "decl i (Memory (MTArray x t)) (Some (KMemptr p, t')) True _ mem _ (c, m, k, e) =
  (if (t' = (Memory (MTArray x t)) \<and> x > 0\<and> denvalue e $$ i = None) then 
   Option.bind (cpm2m p (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m)) x t mem (snd (allocate m)))
    (\<lambda>m'. Some (c, m', astack_dup i (Memory (MTArray x t)) (KMemptr (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m))) (k, e))) else None)"
| "decl i (Memory (MTArray x t)) (Some (KMemptr p, t')) False _ _ _ (c, m, k, e) =
  (if (t' = (Memory (MTArray x t)) \<and> x > 0 \<and> denvalue e $$ i = None) then 
   Some (c, m, astack_dup i (Memory (MTArray x t)) (KMemptr p) (k, e)) else None)"
| "decl i (Memory (MTArray x t)) (Some (KCDptr p, t')) _ cd _ _ (c, m, k, e) =
  (if (t' = (Calldata (MTArray x t)) \<and> x > 0 \<and> denvalue e $$ i = None) then 
   Option.bind (cpm2m p (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m)) x t cd (snd (allocate m)))
    (\<lambda>m'. Some (c, m', astack_dup i (Memory (MTArray x t)) (KMemptr (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m))) (k, e))) else None)"
| "decl i (Memory (MTArray x t)) (Some (KStoptr p, Storage (STArray x' t'))) _ _ _ s (c, m, k, e) =
  (if (cps2mTypeCompatible (STArray x' t') (MTArray x t)\<and> denvalue e $$ i = None) then
   Option.bind (cps2m p (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m)) x' t' s (snd (allocate m))) 
    (\<lambda>m''. Some (c, m'', astack_dup i (Memory (MTArray x t)) (KMemptr (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m))) (k, e))) else None)"
| "decl _ (Memory _) _ _ _ _ _ _ = None"

(* Declaring storage variables *)
| "decl i (Storage (STArray x t)) (Some (KStoptr p, t')) _ _ _ _ (c, m, k, e) =
  (if (t' = (Storage (STArray x t))\<and> denvalue e $$ i = None) then Some (c, m, astack_dup i (Storage (STArray x t)) (KStoptr p) (k, e)) else None)"
| "decl i (Storage (STMap t t')) (Some (KStoptr p, t'')) _ _ _ _ (c, m, k, e) =
   (if (t'' = (Storage (STMap t t'))\<and> denvalue e $$ i = None) then Some (c, m, astack_dup i (Storage (STMap t t')) (KStoptr p) (k, e)) else None)"
| "decl _ (Storage _) _ _ _ _ _ _ = None" (* Uninitialized storage arrays/maps not allowed *)

lemma decl_env:
  assumes "decl a1 a2 a3 cp cd mem sto (c, m, k, env) = Some (c', m', k', env')"
  shows "address env = address env' \<and> sender env = sender env' \<and> svalue env = svalue env' \<and> contract env = contract env'"
  using assms
proof (cases rule:decl.elims)
  case (1 t uu uv uw ux c m k env'')
  then have "address env = address env' \<and>
    sender env = sender env' \<and> svalue env = svalue env' \<and> contract env = contract env'" 
    unfolding astack_dup_env by (auto split:option.splits prod.splits)
  then show ?thesis by blast
next
  case (2 t v t' uy uz va vb c m k e)
  show ?thesis
  proof (cases "convert t' t v")
    case None
    with 2 show ?thesis by simp
  next
    case s: (Some a)
    with 2 s show ?thesis using astack_dup_env[of a1 "Value t" "KValue a" k e k'] by auto
  qed
next
  case (3 vd ve vb vf vg vh vi vj)
  then show ?thesis by simp
next
  case (4 vd ve vb vf vg vh vi vj)
  then show ?thesis by simp
next
  case (5 vd ve vb vf vg vh vi vj)
  then show ?thesis by simp
next
  case (6 vd va ve vf vg vh vi vj)
  then show ?thesis by simp
next
  case (7 vd va ve vf vg vh vi vj)
  then show ?thesis by simp
next
  case (8 vd va ve vf vg vh vi vj)
  then show ?thesis by simp
next
  case (9 x t p vk cd vl vm c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc c)"
  obtain c'' where c_def: "\<exists>x. (x, c'') = allocate c" unfolding allocate_def by simp
  show ?thesis
  proof (cases "cpm2m p l x t cd c''")
    case None
    with 9 l_def c_def show ?thesis unfolding allocate_def by (simp split:if_split_asm)
  next
    case s2: (Some a)
    have " vk = Calldata (MTArray x t) \<and> 0 < x\<and> denvalue env $$ a1 = None" using 9  by (simp split:if_split_asm)
    
    then have set:"Some (a, m, astack_dup a1 (Calldata (MTArray x t)) (KCDptr l) (k, env)) = Some (c', m', k', env') "
    using 9 l_def c_def s2 
    by (metis (mono_tags, lifting) bind.bind_lunit case_prod_conv)
    then have " address env = address env' \<and> contract env = contract env' \<and> sender env = sender env' \<and> svalue env = svalue env'"
      using 9 l_def c_def s2 using astack_dup_env[of a1 "Calldata (MTArray x t)" "KCDptr l" k env k' env'] by blast
    then show ?thesis using 9  by simp

  qed
next
  case (10 x t p vn vo mem vp c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc c)"
  obtain c' where c_def: "\<exists>x. (x, c') = allocate c" unfolding allocate_def by simp
  show ?thesis
  proof (cases "cpm2m p l x t mem c'")
    case None
    with 10 l_def c_def show ?thesis unfolding allocate_def by (simp split:if_split_asm)
  next
    case s2: (Some a)
    with 10 l_def c_def show ?thesis unfolding allocate_def using astack_dup_env[of a1 _ _ k env k' env'] by (simp split:if_split_asm)
  qed
next
  case (11 v vr vs vt vu vv vw)
  then show ?thesis by simp
next
  case (12 vq vs vt vu vv vw)
  then show ?thesis by simp
next
  case (13 vq vc vb vs vt vu vv vw)
  then show ?thesis by simp
next
  case (14 v vc vb vs vt vu vv vw)
  then show ?thesis by simp
next
  case (15 vq vc vb vt vu vv vw)
  then show ?thesis by simp
next
  case (16 vq vc vb vs vt vu vv vw)
  then show ?thesis by simp
next
  case (17 vq vr vt vu vv vw)
  then show ?thesis by simp
next
  case (18 x t vx vy vz wa c m k env)
  then show ?thesis using astack_dup_env[of _ _ _ k env k' env'] by (simp split:if_splits)
next
  case (19 x t p wb wc mem wd c m k env)
  show ?thesis
  proof (cases cp)
    case True
    define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m)"
    obtain m' where m'_def: "\<exists>x. (x, m') = allocate m" unfolding allocate_def by simp
    then show ?thesis
    proof (cases "cpm2m p l x t mem m'")
      case None
      with 19 l_def m'_def show ?thesis unfolding allocate_def by (simp split:if_split_asm)
    next
      case s2: (Some a)
      with 19 l_def m'_def show ?thesis unfolding allocate_def using astack_dup_env[of _ _ _ k env k' env'] by (simp split:if_split_asm)
    qed
  next
    case False
    with 19 show ?thesis by simp
  qed
next
  case (20 x t p we wf wg wh c m k env)
  then show ?thesis using astack_dup_env[of _ _ _ k env k' env'] by  (simp split:if_split_asm)
next
  case (21 x t p wi wj cd wk wl c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m)"
  obtain m' where m'_def: "\<exists>x. (x, m') = allocate m" unfolding allocate_def by simp
  then show ?thesis
  proof (cases "cpm2m p l x t cd m'")
    case None
    with 21 l_def m'_def show ?thesis unfolding allocate_def by  (simp split:if_split_asm)
  next
    case s2: (Some a)
    with 21 l_def m'_def show ?thesis unfolding allocate_def using astack_dup_env[of _ _ _ k env k' env'] by  (simp split:if_split_asm)
  qed
next
  case (22 x t p x' t' wm wn wo s c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m)"
  obtain m' where m'_def: "\<exists>x. (x, m') = allocate m" unfolding allocate_def by simp
  show ?thesis
  proof (cases "cps2m p l x' t' s m'")
    case None
    with 22 l_def m'_def show ?thesis unfolding allocate_def by (simp split:if_split_asm)
  next
    case s2: (Some a)
    with 22 l_def m'_def show ?thesis unfolding allocate_def using astack_dup_env[of _ _ _ k env k' env'] by (simp split:if_split_asm)
  qed
next
  case (23 v wr ws wt wu wv ww)
  then show ?thesis by simp
next
  case (24 va v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (25 wq vc vb ws wt wu wv ww)
  then show ?thesis by simp
next
  case (26 v vc vb ws wt wu wv ww)
  then show ?thesis by simp
next
  case (27 v vc vb ws wt wu wv ww)
  then show ?thesis by simp
next
  case (28 wq vc v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (29 wq vc v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (30 wq vc v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (31 wq vc va vd ws wt wu wv ww)
  then show ?thesis by simp
next
  case (32 wq vc va ws wt wu wv ww)
  then show ?thesis by simp
next
  case (33 va v wt wu wv ww)
  then show ?thesis by simp
next
  case (34 wq vc vb wt wu wv ww)
  then show ?thesis by simp
next
  case (35 v vc vb wt wu wv ww)
  then show ?thesis by simp
next
  case (36 v vc vb wt wu wv ww)
  then show ?thesis by simp
next
  case (37 wq vc v wt wu wv ww)
  then show ?thesis by simp
next
  case (38 wq vc v wt wu wv ww)
  then show ?thesis by simp
next
  case (39 wq vc v wt wu wv ww)
  then show ?thesis by simp
next
  case (40 wq vc va vd wt wu wv ww)
  then show ?thesis by simp
next
  case (41 wq vc va wt wu wv ww)
  then show ?thesis by simp
next
  case (42 x t p wx wy wz xa xb c m k env)
  then show ?thesis using astack_dup_env[of _ _ _ k env k' env'] by (simp split:if_split_asm)
next
  case (43 t t' p xc xd xe xf xg c m k e)
  then show ?thesis using astack_dup_env[of _ _ _ k env k' env'] by (simp split:if_split_asm)
next
  case (44 v va xk xl xm xn xo)
  then show ?thesis by simp
next
  case (45 v va ve vd xk xl xm xn xo)
  then show ?thesis by simp
next
  case (46 v va ve vd xk xl xm xn xo)
  then show ?thesis by simp
next
  case (47 v va ve vd xk xl xm xn xo)
  then show ?thesis by simp
next
  case (48 v xj xk xl xm xn xo)
  then show ?thesis by simp
next
  case (49 xi xk xl xm xn xo)
  then show ?thesis by simp
next
  case (50 xi vc vb xk xl xm xn xo)
  then show ?thesis by simp
next
  case (51 xi vc vb xk xl xm xn xo)
  then show ?thesis by simp
next
  case (52 xi vc vb xk xl xm xn xo)
  then show ?thesis by simp
qed

lemma decl_env_subset_denval:
  assumes "decl a1 a2 a3 cp cd mem sto (c, m, k, env) = Some (c', m', k', env')"
  shows "fmdom (denvalue env) |\<subseteq>| fmdom (denvalue env') 
        "
  using assms
proof (cases rule:decl.elims)
  case (1 t uu uv uw ux c m k env)
  then show ?thesis using astack_dup_den_sub[of env] by (auto split:option.splits)
next
  case (2 t v t' uy uz va vb c m k e)
  show ?thesis
  proof (cases "convert t' t v")
    case None
    with 2 show ?thesis by simp
  next
    case s: (Some a)
    with 2 s show ?thesis using astack_dup_den_sub by (auto split:option.splits)
  qed
next
  case (3 vd ve vb vf vg vh vi vj)
  then show ?thesis by simp
next
  case (4 vd ve vb vf vg vh vi vj)
  then show ?thesis by simp
next
  case (5 vd ve vb vf vg vh vi vj)
  then show ?thesis by simp
next
  case (6 vd va ve vf vg vh vi vj)
  then show ?thesis by simp
next
  case (7 vd va ve vf vg vh vi vj)
  then show ?thesis by simp
next
  case (8 vd va ve vf vg vh vi vj)
  then show ?thesis by simp
next
  case (9 x t p vk cd vl vm c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc c)"
  obtain c' where c_def: "\<exists>x. (x, c') = allocate c" unfolding allocate_def by simp
  show ?thesis
  proof (cases "cpm2m p l x t cd c'")
    case None
    with 9 l_def c_def show ?thesis unfolding allocate_def by (simp split:if_split_asm)
  next
    case s2: (Some a)
    with 9 l_def c_def show ?thesis unfolding allocate_def using astack_dup_den_sub astack_den_sub by (simp split:if_split_asm option.splits)
  qed
next
  case (10 x t p vn vo mem vp c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc c)"
  obtain c' where c_def: "\<exists>x. (x, c') = allocate c" unfolding allocate_def by simp
  show ?thesis
  proof (cases "cpm2m p l x t mem c'")
    case None
    with 10 l_def c_def show ?thesis unfolding allocate_def by (simp split:if_split_asm)
  next
    case s2: (Some a)
    then have "vn = Memory (MTArray x t) \<and> 0 < x\<and> denvalue env $$ a1 = None" using 10 by (simp split:if_split_asm)
    then have "(k', env') = astack_dup a1 (Calldata (MTArray x t)) (KCDptr l) (k, env)"
      using 10 l_def c_def s2 unfolding allocate_def by simp
    then show ?thesis unfolding allocate_def using astack_dup_den_sub[of env a1 "Calldata (MTArray x t)" "KCDptr l" k] 
      by (metis "10"(7) snd_conv)
  qed
next
  case (11 v vr vs vt vu vv vw)
  then show ?thesis by simp
next
  case (12 vq vs vt vu vv vw)
  then show ?thesis by simp
next
  case (13 vq vc vb vs vt vu vv vw)
  then show ?thesis by simp
next
  case (14 v vc vb vs vt vu vv vw)
  then show ?thesis by simp
next
  case (15 vq vc vb vt vu vv vw)
  then show ?thesis by simp
next
  case (16 vq vc vb vs vt vu vv vw)
  then show ?thesis by simp
next
  case (17 vq vr vt vu vv vw)
  then show ?thesis by simp
next
  case (18 x t vx vy vz wa c m k env)
  then show ?thesis using astack_den_sub by (simp split:if_split_asm option.splits)
next
  case (19 x t p wb wc mem wd c m k env)
  show ?thesis
  proof (cases cp)
    case True
    define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m)"
    obtain m' where m'_def: "\<exists>x. (x, m') = allocate m" unfolding allocate_def by simp
    then show ?thesis
    proof (cases "cpm2m p l x t mem m'")
      case None
      with 19 l_def m'_def show ?thesis unfolding allocate_def by (simp split:if_split_asm)
    next
      case s2: (Some a)
      with 19 l_def m'_def show ?thesis unfolding allocate_def using astack_dup_den_sub[of env a1 "Memory (MTArray x t)"] by (simp split:if_split_asm option.splits)
    qed
  next
    case False
    with 19 show ?thesis by simp
  qed
next
  case (20 x t p we wf wg wh c m k env)
  then show ?thesis using astack_den_sub  by (simp split:if_split_asm option.splits)
next
  case (21 x t p wi wj cd wk wl c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m)"
  obtain m' where m'_def: "\<exists>x. (x, m') = allocate m" unfolding allocate_def by simp
  then show ?thesis
  proof (cases "cpm2m p l x t cd m'")
    case None
    with 21 l_def m'_def show ?thesis unfolding allocate_def by  (simp split:if_split_asm)
  next
    case s2: (Some a)
    with 21 l_def m'_def show ?thesis unfolding allocate_def using astack_dup_den_sub[of env a1] by (simp split:if_split_asm option.splits)
  qed
next
  case (22 x t p x' t' wm wn wo s c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m)"
  obtain m' where m'_def: "\<exists>x. (x, m') = allocate m" unfolding allocate_def by simp
  show ?thesis
  proof (cases "cps2m p l x' t' s m'")
    case None
    with 22 l_def m'_def show ?thesis unfolding allocate_def by (simp split:if_split_asm)
  next
    case s2: (Some a)
    with 22 l_def m'_def show ?thesis unfolding allocate_def using  astack_dup_den_sub[of env a1]  by (simp split:if_split_asm option.splits)
  qed
next
  case (23 v wr ws wt wu wv ww)
  then show ?thesis by simp
next
  case (24 va v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (25 wq vc vb ws wt wu wv ww)
  then show ?thesis by simp
next
  case (26 v vc vb ws wt wu wv ww)
  then show ?thesis by simp
next
  case (27 v vc vb ws wt wu wv ww)
  then show ?thesis by simp
next
  case (28 wq vc v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (29 wq vc v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (30 wq vc v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (31 wq vc va vd ws wt wu wv ww)
  then show ?thesis by simp
next
  case (32 wq vc va ws wt wu wv ww)
  then show ?thesis by simp
next
  case (33 va v wt wu wv ww)
  then show ?thesis by simp
next
  case (34 wq vc vb wt wu wv ww)
  then show ?thesis by simp
next
  case (35 v vc vb wt wu wv ww)
  then show ?thesis by simp
next
  case (36 v vc vb wt wu wv ww)
  then show ?thesis by simp
next
  case (37 wq vc v wt wu wv ww)
  then show ?thesis by simp
next
  case (38 wq vc v wt wu wv ww)
  then show ?thesis by simp
next
  case (39 wq vc v wt wu wv ww)
  then show ?thesis by simp
next
  case (40 wq vc va vd wt wu wv ww)
  then show ?thesis by simp
next
  case (41 wq vc va wt wu wv ww)
  then show ?thesis by simp
next
  case (42 x t p wx wy wz xa xb c m k env)
  then show ?thesis using astack_den_sub astack_dup_den_sub  by (simp split:if_split_asm option.splits)
next
  case (43 t t' p xc xd xe xf xg c m k e)
  then show ?thesis using astack_den_sub astack_dup_den_sub  by (simp split:if_split_asm option.splits)
next
  case (44 v va xk xl xm xn xo)
  then show ?thesis by simp
next
  case (45 v va ve vd xk xl xm xn xo)
  then show ?thesis by simp
next
  case (46 v va ve vd xk xl xm xn xo)
  then show ?thesis by simp
next
  case (47 v va ve vd xk xl xm xn xo)
  then show ?thesis by simp
next
  case (48 v xj xk xl xm xn xo)
  then show ?thesis by simp
next
  case (49 xi xk xl xm xn xo)
  then show ?thesis by simp
next
  case (50 xi vc vb xk xl xm xn xo)
  then show ?thesis by simp
next
  case (51 xi vc vb xk xl xm xn xo)
  then show ?thesis by simp
next
  case (52 xi vc vb xk xl xm xn xo)
  then show ?thesis by simp
qed



lemma decl_env_kval:
  assumes "decl i (Value t) a3 cp cd mem sto (c, m, k, env) = Some (c', m', k', env')"
    and "denvalue env $$ i = None"
  shows "\<exists>t l. denvalue env' $$ i = Some (Value t, Stackloc l)"
  using assms
proof (cases rule:decl.elims)
  case (1 t uu uv uw ux c m k env)
  then show ?thesis using assms(2) by (auto split:option.splits)
next
  case (2 t v t' uy uz va vb c m k e)
  show ?thesis
  proof (cases "convert t' t v")
    case None
    with 2 show ?thesis by simp
  next
    case s: (Some a)
    with 2 s show ?thesis using assms(2) by (auto split:option.splits)
  qed
next
  case (3 vd ve vb vf vg vh vi vj)
  then show ?thesis by simp
next
  case (4 vd ve vb vf vg vh vi vj)
  then show ?thesis by simp
next
  case (5 vd ve vb vf vg vh vi vj)
  then show ?thesis by simp
next
  case (6 vd va ve vf vg vh vi vj)
  then show ?thesis by simp
next
  case (7 vd va ve vf vg vh vi vj)
  then show ?thesis by simp
next
  case (8 vd va ve vf vg vh vi vj)
  then show ?thesis by simp
next
  case (9 x t p vk cd vl vm c m k env)
  then show ?thesis by auto
next
  case (10 x t p vn vo mem vp c m k env)
  then show ?thesis by auto
next
  case (11 v vr vs vt vu vv vw)
  then show ?thesis by simp
next
  case (12 vq vs vt vu vv vw)
  then show ?thesis by simp
next
  case (13 vq vc vb vs vt vu vv vw)
  then show ?thesis by simp
next
  case (14 v vc vb vs vt vu vv vw)
  then show ?thesis by simp
next
  case (15 vq vc vb vt vu vv vw)
  then show ?thesis by simp
next
  case (16 vq vc vb vs vt vu vv vw)
  then show ?thesis by simp
next
  case (17 vq vr vt vu vv vw)
  then show ?thesis by simp
next
  case (18 x t vx vy vz wa c m k env)
  then show ?thesis using astack_den_sub by simp
next
  case (19 x t p wb wc mem wd c m k env)
  then show ?thesis by auto
next
  case (20 x t p we wf wg wh c m k env)
  then show ?thesis by auto
next
  case (21 x t p wi wj cd wk wl c m k env)
  then show ?thesis by auto
next
  case (22 x t p x' t' wm wn wo s c m k env)
  then show ?thesis by auto
next
  case (23 v wr ws wt wu wv ww)
  then show ?thesis by simp
next
  case (24 va v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (25 wq vc vb ws wt wu wv ww)
  then show ?thesis by simp
next
  case (26 v vc vb ws wt wu wv ww)
  then show ?thesis by simp
next
  case (27 v vc vb ws wt wu wv ww)
  then show ?thesis by simp
next
  case (28 wq vc v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (29 wq vc v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (30 wq vc v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (31 wq vc va vd ws wt wu wv ww)
  then show ?thesis by simp
next
  case (32 wq vc va ws wt wu wv ww)
  then show ?thesis by simp
next
  case (33 va v wt wu wv ww)
  then show ?thesis by simp
next
  case (34 wq vc vb wt wu wv ww)
  then show ?thesis by simp
next
  case (35 v vc vb wt wu wv ww)
  then show ?thesis by simp
next
  case (36 v vc vb wt wu wv ww)
  then show ?thesis by simp
next
  case (37 wq vc v wt wu wv ww)
  then show ?thesis by simp
next
  case (38 wq vc v wt wu wv ww)
  then show ?thesis by simp
next
  case (39 wq vc v wt wu wv ww)
  then show ?thesis by simp
next
  case (40 wq vc va vd wt wu wv ww)
  then show ?thesis by simp
next
  case (41 wq vc va wt wu wv ww)
  then show ?thesis by simp
next
  case (42 x t p wx wy wz xa xb c m k env)
  then show ?thesis using astack_den_sub by (simp split:if_split_asm)
next
  case (43 t t' p xc xd xe xf xg c m k e)
  then show ?thesis using astack_den_sub by (simp split:if_split_asm)
next
  case (44 v va xk xl xm xn xo)
  then show ?thesis by simp
next
  case (45 v va ve vd xk xl xm xn xo)
  then show ?thesis by simp
next
  case (46 v va ve vd xk xl xm xn xo)
  then show ?thesis by simp
next
  case (47 v va ve vd xk xl xm xn xo)
  then show ?thesis by simp
next
  case (48 v xj xk xl xm xn xo)
  then show ?thesis by simp
next
  case (49 xi xk xl xm xn xo)
  then show ?thesis by simp
next
  case (50 xi vc vb xk xl xm xn xo)
  then show ?thesis by simp
next
  case (51 xi vc vb xk xl xm xn xo)
  then show ?thesis by simp
next
  case (52 xi vc vb xk xl xm xn xo)
  then show ?thesis by simp
qed

lemma decl_env_memory:
  assumes "decl i (Memory t) a3 cp cd mem sto (c, m, k, env) = Some (c', m', k', env')"
and "denvalue env $$ i = None"
  shows "denvalue env' $$ i = Some (Memory t, Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc k)))
          \<and> (accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc k)) k' = Some (KMemptr (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m))) \<or> (\<exists>v t'. a3 = Some(KMemptr v,Memory t') \<and> accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc k)) k' = Some (KMemptr v)))"
  using assms
proof (cases rule:decl.elims)
  case (1 t uu uv uw ux c m k env)
  then show ?thesis by auto
next
  case (2 t v t' uy uz va vb c m k e)
  show ?thesis
  proof (cases "convert t' t v")
    case None
    with 2 show ?thesis by simp
  next
    case s: (Some a)
    with 2 s show ?thesis by auto
  qed
next
  case (3 vd ve vb vf vg vh vi vj)
  then show ?thesis by simp
next
  case (4 vd ve vb vf vg vh vi vj)
  then show ?thesis by simp
next
  case (5 vd ve vb vf vg vh vi vj)
  then show ?thesis by simp
next
  case (6 vd va ve vf vg vh vi vj)
  then show ?thesis by simp
next
  case (7 vd va ve vf vg vh vi vj)
  then show ?thesis by simp
next
  case (8 vd va ve vf vg vh vi vj)
  then show ?thesis by simp
next
  case (9 x t p vk cd vl vm c m k env)
  then show ?thesis by auto
next
  case (10 x t p vn vo mem vp c m k env)
  then show ?thesis by auto
next
  case (11 v vr vs vt vu vv vw)
  then show ?thesis by simp
next
  case (12 vq vs vt vu vv vw)
  then show ?thesis by simp
next
  case (13 vq vc vb vs vt vu vv vw)
  then show ?thesis by simp
next
  case (14 v vc vb vs vt vu vv vw)
  then show ?thesis by simp
next
  case (15 vq vc vb vt vu vv vw)
  then show ?thesis by simp
next
  case (16 vq vc vb vs vt vu vv vw)
  then show ?thesis by simp
next
  case (17 vq vr vt vu vv vw)
  then show ?thesis by simp
next
  case (18 x t vx vy vz wa c m k env)
  then have "accessStore \<lfloor>toploc k\<rfloor> k' = Some (KMemptr \<lfloor>toploc m\<rfloor>)" using assms
    unfolding astack_dup.simps push_def updateStore_def accessStore_def allocate_def by (auto split:option.splits if_splits)
  then show ?thesis using astack_dup_den_sub 18 assms(2) by (auto split:option.splits if_splits)
next
  case (19 x t p wb wc mem wd c m k env)
  then have *:"wb = Memory (MTArray x t) \<and> 0 < x\<and> denvalue env $$ i = None" by (simp split:if_splits)
  then obtain m'' where "cpm2m p \<lfloor>toploc m\<rfloor> x t mem (snd (allocate m)) = Some m''" using 19 by fastforce
  then have "(k', env') = astack i (Memory (MTArray x t)) (KMemptr \<lfloor>toploc m\<rfloor>) (k, env)"
    using 19 * assms by simp
  then show ?thesis unfolding astack.simps updateEnv.simps using 19(1,7) unfolding 
        astack.simps push_def updateStore_def accessStore_def allocate_def
    by auto
next
  case (20 x t p we wf wg wh c m k env)
  then have *:"we = Memory (MTArray x t) \<and> 0 < x" by (simp split:if_splits)
  then have "(k', env') = astack i (Memory (MTArray x t)) (KMemptr p) (k, env)" using assms(2) 20 by auto
  then show ?thesis unfolding astack.simps updateEnv.simps push_def updateStore_def accessStore_def allocate_def using 20 by auto
next
  case (21 x t p wi wj cd wk wl c m k env)
  then have *:"wi = Calldata (MTArray x t) \<and> 0 < x\<and> denvalue env $$ i = None" by (simp split:if_splits) 
  then obtain m'' where "cpm2m p \<lfloor>toploc m\<rfloor> x t cd (snd (allocate m)) = Some m''" using 21 by fastforce
  then have "(k', env') = astack i (Memory (MTArray x t)) (KMemptr \<lfloor>toploc m\<rfloor>) (k, env)" using 21 * assms(2) by auto
  then show ?thesis unfolding astack.simps updateEnv.simps  push_def updateStore_def accessStore_def allocate_def using 21 by auto
next
  case (22 x t p x' t' wm wn wo s c m k env)
  then have *:"cps2mTypeCompatible (STArray x' t') (MTArray x t)\<and> denvalue env $$ i = None" by (simp split:if_splits)
  then obtain m'' where "cps2m p \<lfloor>toploc m\<rfloor> x' t' s (snd (allocate m)) = Some m''" using 22 by fastforce
  then have "(k', env') = astack i (Memory (MTArray x t)) (KMemptr \<lfloor>toploc m\<rfloor>) (k, env)" using 22 * assms(2) by auto
  then show ?thesis unfolding astack.simps updateEnv.simps  push_def updateStore_def accessStore_def allocate_def using 22 by auto
next
  case (23 v wr ws wt wu wv ww)
  then show ?thesis by simp
next
  case (24 va v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (25 wq vc vb ws wt wu wv ww)
  then show ?thesis by simp
next
  case (26 v vc vb ws wt wu wv ww)
  then show ?thesis by simp
next
  case (27 v vc vb ws wt wu wv ww)
  then show ?thesis by simp
next
  case (28 wq vc v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (29 wq vc v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (30 wq vc v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (31 wq vc va vd ws wt wu wv ww)
  then show ?thesis by simp
next
  case (32 wq vc va ws wt wu wv ww)
  then show ?thesis by simp
next
  case (33 va v wt wu wv ww)
  then show ?thesis by simp
next
  case (34 wq vc vb wt wu wv ww)
  then show ?thesis by simp
next
  case (35 v vc vb wt wu wv ww)
  then show ?thesis by simp
next
  case (36 v vc vb wt wu wv ww)
  then show ?thesis by simp
next
  case (37 wq vc v wt wu wv ww)
  then show ?thesis by simp
next
  case (38 wq vc v wt wu wv ww)
  then show ?thesis by simp
next
  case (39 wq vc v wt wu wv ww)
  then show ?thesis by simp
next
  case (40 wq vc va vd wt wu wv ww)
  then show ?thesis by simp
next
  case (41 wq vc va wt wu wv ww)
  then show ?thesis by simp
next
  case (42 x t p wx wy wz xa xb c m k env)
  then show ?thesis using astack_den_sub by (simp split:if_split_asm)
next
  case (43 t t' p xc xd xe xf xg c m k e)
  then show ?thesis using astack_den_sub by (simp split:if_split_asm)
next
  case (44 v va xk xl xm xn xo)
  then show ?thesis by simp
next
  case (45 v va ve vd xk xl xm xn xo)
  then show ?thesis by simp
next
  case (46 v va ve vd xk xl xm xn xo)
  then show ?thesis by simp
next
  case (47 v va ve vd xk xl xm xn xo)
  then show ?thesis by simp
next
  case (48 v xj xk xl xm xn xo)
  then show ?thesis by simp
next
  case (49 xi xk xl xm xn xo)
  then show ?thesis by simp
next
  case (50 xi vc vb xk xl xm xn xo)
  then show ?thesis by simp
next
  case (51 xi vc vb xk xl xm xn xo)
  then show ?thesis by simp
next
  case (52 xi vc vb xk xl xm xn xo)
  then show ?thesis by simp
qed

lemma decl_env_storage:
  assumes "decl i tp a3 cp cd mem sto (c, m, k, env) = Some (c', m', k', env')"
    and "\<forall>stp. tp \<noteq> Storage stp"
    and "denvalue env $$ i = None"
  shows "\<forall>t l. denvalue env' $$ i = Some (t, l) \<longrightarrow> (\<forall>stl tp. l \<noteq> Storeloc stl \<and> t \<noteq> Storage tp)"
  using assms
proof (cases rule:decl.elims)
  case (1 t uu uv uw ux c m k env)
  then show ?thesis using assms by auto
next
  case (2 t v t' uy uz va vb c m k e)
  show ?thesis
  proof (cases "convert t' t v")
    case None
    with 2 show ?thesis by simp
  next
    case s: (Some a)
    with 2 s show ?thesis using assms by auto
  qed
next
  case (3 vd ve vb vf vg vh vi vj)
  then show ?thesis by simp
next
  case (4 vd ve vb vf vg vh vi vj)
  then show ?thesis by simp
next
  case (5 vd ve vb vf vg vh vi vj)
  then show ?thesis by simp
next
  case (6 vd va ve vf vg vh vi vj)
  then show ?thesis by simp
next
  case (7 vd va ve vf vg vh vi vj)
  then show ?thesis by simp
next
  case (8 vd va ve vf vg vh vi vj)
  then show ?thesis by simp
next
  case (9 x t p vk cd vl vm c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc c)"
  obtain c' where c_def: "\<exists>x. (x, c') = allocate c" unfolding allocate_def by simp
  show ?thesis
  proof (cases "cpm2m p l x t cd c'")
    case None
    with 9 l_def c_def show ?thesis unfolding allocate_def by (simp split:if_split_asm)
  next
    case s2: (Some a)
    with 9 l_def c_def show ?thesis unfolding allocate_def using astack_den_sub using assms by (simp split:if_split_asm)
  qed
next
  case (10 x t p vn vo mem vp c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc c)"
  obtain c' where c_def: "\<exists>x. (x, c') = allocate c" unfolding allocate_def by simp
  show ?thesis
  proof (cases "cpm2m p l x t mem c'")
    case None
    with 10 l_def c_def show ?thesis unfolding allocate_def by (simp split:if_split_asm)
  next
    case s2: (Some a)
    with 10 l_def c_def show ?thesis unfolding allocate_def using astack_den_sub using assms by (simp split:if_split_asm)
  qed
next
  case (11 v vr vs vt vu vv vw)
  then show ?thesis by simp
next
  case (12 vq vs vt vu vv vw)
  then show ?thesis by simp
next
  case (13 vq vc vb vs vt vu vv vw)
  then show ?thesis by simp
next
  case (14 v vc vb vs vt vu vv vw)
  then show ?thesis by simp
next
  case (15 vq vc vb vt vu vv vw)
  then show ?thesis by simp
next
  case (16 vq vc vb vs vt vu vv vw)
  then show ?thesis by simp
next
  case (17 vq vr vt vu vv vw)
  then show ?thesis by simp
next
  case (18 x t vx vy vz wa c m k env)
  then show ?thesis using astack_den_sub using assms by (auto split:option.splits if_splits)
next
  case (19 x t p wb wc mem wd c m k env)
  show ?thesis
  proof (cases cp)
    case True
    define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m)"
    obtain m' where m'_def: "\<exists>x. (x, m') = allocate m" unfolding allocate_def by simp
    then show ?thesis
    proof (cases "cpm2m p l x t mem m'")
      case None
      with 19 l_def m'_def show ?thesis unfolding allocate_def by (simp split:if_split_asm)
    next
      case s2: (Some a)
      with 19 l_def m'_def show ?thesis unfolding allocate_def using astack_den_sub using assms by (simp split:if_split_asm)
    qed
  next
    case False
    with 19 show ?thesis by simp
  qed
next
  case (20 x t p we wf wg wh c m k env)
  then show ?thesis using astack_den_sub assms by  (simp split:if_split_asm)
next
  case (21 x t p wi wj cd wk wl c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m)"
  obtain m' where m'_def: "\<exists>x. (x, m') = allocate m" unfolding allocate_def by simp
  then show ?thesis
  proof (cases "cpm2m p l x t cd m'")
    case None
    with 21 l_def m'_def show ?thesis unfolding allocate_def by  (simp split:if_split_asm)
  next
    case s2: (Some a)
    with 21 l_def m'_def show ?thesis unfolding allocate_def using astack_den_sub using assms by  (simp split:if_split_asm)
  qed
next
  case (22 x t p x' t' wm wn wo s c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m)"
  obtain m' where m'_def: "\<exists>x. (x, m') = allocate m" unfolding allocate_def by simp
  show ?thesis
  proof (cases "cps2m p l x' t' s m'")
    case None
    with 22 l_def m'_def show ?thesis unfolding allocate_def by (simp split:if_split_asm)
  next
    case s2: (Some a)
    with 22 l_def m'_def show ?thesis unfolding allocate_def using  astack_den_sub using assms by (simp split:if_split_asm)
  qed
next
  case (23 v wr ws wt wu wv ww)
  then show ?thesis by simp
next
  case (24 va v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (25 wq vc vb ws wt wu wv ww)
  then show ?thesis by simp
next
  case (26 v vc vb ws wt wu wv ww)
  then show ?thesis by simp
next
  case (27 v vc vb ws wt wu wv ww)
  then show ?thesis by simp
next
  case (28 wq vc v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (29 wq vc v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (30 wq vc v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (31 wq vc va vd ws wt wu wv ww)
  then show ?thesis by simp
next
  case (32 wq vc va ws wt wu wv ww)
  then show ?thesis by simp
next
  case (33 va v wt wu wv ww)
  then show ?thesis by simp
next
  case (34 wq vc vb wt wu wv ww)
  then show ?thesis by simp
next
  case (35 v vc vb wt wu wv ww)
  then show ?thesis by simp
next
  case (36 v vc vb wt wu wv ww)
  then show ?thesis by simp
next
  case (37 wq vc v wt wu wv ww)
  then show ?thesis by simp
next
  case (38 wq vc v wt wu wv ww)
  then show ?thesis by simp
next
  case (39 wq vc v wt wu wv ww)
  then show ?thesis by simp
next
  case (40 wq vc va vd wt wu wv ww)
  then show ?thesis by simp
next
  case (41 wq vc va wt wu wv ww)
  then show ?thesis by simp
next
  case (42 x t p wx wy wz xa xb c m k env)
  then show ?thesis using astack_den_sub assms by (simp split:if_split_asm)
next
  case (43 t t' p xc xd xe xf xg c m k e)
  then show ?thesis using astack_den_sub assms by (simp split:if_split_asm)
next
  case (44 v va xk xl xm xn xo)
  then show ?thesis by simp
next
  case (45 v va ve vd xk xl xm xn xo)
  then show ?thesis by simp
next
  case (46 v va ve vd xk xl xm xn xo)
  then show ?thesis by simp
next
  case (47 v va ve vd xk xl xm xn xo)
  then show ?thesis by simp
next
  case (48 v xj xk xl xm xn xo)
  then show ?thesis by simp
next
  case (49 xi xk xl xm xn xo)
  then show ?thesis by simp
next
  case (50 xi vc vb xk xl xm xn xo)
  then show ?thesis by simp
next
  case (51 xi vc vb xk xl xm xn xo)
  then show ?thesis by simp
next
  case (52 xi vc vb xk xl xm xn xo)
  then show ?thesis by simp
qed

lemma decl_stack_change:
  assumes "decl a1 a2 a3 cp cd mem sto (c, m, k, env) = Some (c', m', k', env')"
    and "l \<noteq>(ShowL\<^sub>n\<^sub>a\<^sub>t (toploc k))"  
  shows "( accessStore l k = accessStore l k')"
  using assms
proof (cases rule:decl.elims)
  case (1 t uu uv uw ux c m k env)
  then have a1:"k' = (let s = updateStore \<lfloor>toploc k\<rfloor> (KValue (ival t)) k in snd (allocate s)) \<or> k' = k"
    unfolding astack_dup.simps push_def  using assms by (auto split:option.splits)
  then have "\<forall>l. l \<noteq> \<lfloor>toploc k\<rfloor>  \<longrightarrow> accessStore l k' = accessStore l k" unfolding allocate_def updateStore_def accessStore_def by (auto split:option.splits)
  then show ?thesis using 1 assms by simp

next
  case (2 t v t' uy uz va vb c m k e)
  show ?thesis
  proof (cases "convert t' t v")
    case None
    with 2 show ?thesis by simp
  next
    case s: (Some a)
    then have "(k',env') = (astack_dup a1 (Value t) (KValue a)  (k, e))" using 2 by simp
    then have "k' = (let s = updateStore \<lfloor>toploc k\<rfloor> (KValue a) k in snd (allocate s)) \<or> k' = k"
      unfolding astack_dup.simps push_def  by (auto split:option.splits)
    then have "\<forall>l. l \<noteq> \<lfloor>toploc k\<rfloor>  \<longrightarrow> accessStore l k' = accessStore l k" unfolding allocate_def updateStore_def accessStore_def by (auto split:option.splits)
    with 2 s assms show ?thesis  by auto
  qed
next
  case (3 vd ve vb vf vg vh vi vj)
  then show ?thesis by simp
next
  case (4 vd ve vb vf vg vh vi vj)
  then show ?thesis by simp
next
  case (5 vd ve vb vf vg vh vi vj)
  then show ?thesis by simp
next
  case (6 vd va ve vf vg vh vi vj)
  then show ?thesis by simp
next
  case (7 vd va ve vf vg vh vi vj)
  then show ?thesis by simp
next
  case (8 vd va ve vf vg vh vi vj)
  then show ?thesis by simp
next
  case (9 x t p vk cd vl vm c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc c)"
  obtain c'' where c_def: "\<exists>x. (x, c'') = allocate c" unfolding allocate_def by simp
  show ?thesis
  proof (cases "cpm2m p l x t cd c''")
    case None
    with 9 l_def c_def show ?thesis unfolding allocate_def by (simp split:if_split_asm)
  next
    case s2: (Some a)
    then have "vk = Calldata (MTArray x t) \<and> 0 < x \<and> denvalue env $$ a1 = None" using 9 
      by (meson option.discI)
    then have "Some (c', m', k', env') =
    (cpm2m p l x t cd c'' \<bind> (\<lambda>c''. Some (c'', m, astack_dup a1 (Calldata (MTArray x t)) (KCDptr l) (k, env))))" using 9 l_def c_def 
      by (metis case_prod_conv)
    then have "Some (c', m', k', env') = Some (a, m, astack_dup a1 (Calldata (MTArray x t)) (KCDptr l) (k, env))" using s2 by simp
    then have "(k',env') = astack_dup a1 (Calldata (MTArray x t)) (KCDptr l) (k, env)" using 9 by (auto split:option.splits)
    then have "k' = (let s = updateStore \<lfloor>toploc k\<rfloor> (KCDptr l) k in snd (allocate s)) \<or> k' = k"
      unfolding astack_dup.simps push_def by (auto split:option.splits)
    then have "\<forall>l. l \<noteq> \<lfloor>toploc k\<rfloor>  \<longrightarrow> accessStore l k' = accessStore l k" unfolding allocate_def updateStore_def accessStore_def by (auto split:option.splits)
    then  show ?thesis using 9 l_def c_def assms unfolding allocate_def using astack_den_sub by (simp split:if_split_asm)
  qed
next
  case (10 x t p vn vo mem vp c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc c)"
  obtain c'' where c_def: "\<exists>x. (x, c'') = allocate c" unfolding allocate_def by simp
  show ?thesis
  proof (cases "cpm2m p l x t mem c''")
    case None
    with 10 l_def c_def show ?thesis unfolding allocate_def by (simp split:if_split_asm)
  next
    case s2: (Some a)
    then have "vn = Memory (MTArray x t) \<and> 0 < x\<and> denvalue env $$ a1 = None" using 10
      by (meson option.discI)
    then have "Some (c', m', k', env') =
    (cpm2m p l x t mem c'' \<bind> (\<lambda>c''. Some (c'', m, astack_dup a1 (Calldata (MTArray x t)) (KCDptr l) (k, env))))" using 10 l_def c_def 
      by (metis case_prod_conv)
    then have "Some (c', m', k', env') = Some (a, m, astack_dup a1 (Calldata (MTArray x t)) (KCDptr l) (k, env))" using s2 by simp
    then have "(k',env') = astack_dup a1 (Calldata (MTArray x t)) (KCDptr l) (k, env)" using 10 by simp
    then have "k' = (let s = updateStore \<lfloor>toploc k\<rfloor> (KCDptr l) k in snd (allocate s)) \<or> k = k'"
      unfolding astack_dup.simps push_def  by (auto split:option.splits)
    then have "\<forall>l. l \<noteq> \<lfloor>toploc k\<rfloor>  \<longrightarrow> accessStore l k' = accessStore l k" unfolding allocate_def updateStore_def accessStore_def by (auto split:option.splits)
    with 10 l_def c_def show ?thesis unfolding allocate_def using astack_den_sub assms by (simp split:if_split_asm)
  qed
next
  case (11 v vr vs vt vu vv vw)
  then show ?thesis by simp
next
  case (12 vq vs vt vu vv vw)
  then show ?thesis by simp
next
  case (13 vq vc vb vs vt vu vv vw)
  then show ?thesis by simp
next
  case (14 v vc vb vs vt vu vv vw)
  then show ?thesis by simp
next
  case (15 vq vc vb vt vu vv vw)
  then show ?thesis by simp
next
  case (16 vq vc vb vs vt vu vv vw)
  then show ?thesis by simp
next
  case (17 vq vr vt vu vv vw)
  then show ?thesis by simp
next
  case (18 x t vx vy vz wa c m k env)
  then have "(k', env') = astack_dup a1 (Memory (MTArray x t)) (KMemptr \<lfloor>toploc m\<rfloor>) (k, env)" by (simp split:if_splits)
  then have "k' = (let s = updateStore \<lfloor>toploc k\<rfloor> (KMemptr \<lfloor>toploc m\<rfloor>) k in snd (allocate s)) \<or> k' = k"
      unfolding astack_dup.simps push_def  by (auto split:option.splits)
    then have "\<forall>l. l \<noteq> \<lfloor>toploc k\<rfloor>  \<longrightarrow> accessStore l k' = accessStore l k" unfolding allocate_def updateStore_def accessStore_def by (auto split:option.splits)
  then show ?thesis using astack_den_sub assms 18 by simp
next
  case (19 x t p wb wc mem wd c m k env)
  show ?thesis
  proof (cases cp)
    case True
    define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m)"
    obtain m'' where m'_def: "\<exists>x. (x, m'') = allocate m" unfolding allocate_def by simp
    then show ?thesis
    proof (cases "cpm2m p l x t mem m''")
      case None
      with 19 l_def m'_def show ?thesis unfolding allocate_def by (simp split:if_split_asm)
    next
      case s2: (Some a)
      then have " wb = Memory (MTArray x t) \<and> 0 < x\<and> denvalue env $$ a1 = None" using 19
      by (meson option.discI)
    then have "Some (c', m', k', env') =
    (cpm2m p \<lfloor>toploc m\<rfloor> x t mem (snd (allocate m)) \<bind> (\<lambda>m'. Some (c, m', astack_dup a1 (Memory (MTArray x t)) (KMemptr \<lfloor>toploc m\<rfloor>) (k, env))))" using 19 l_def  
      by simp
    then have "Some (c', m', k', env') = Some (c, a, astack_dup a1 (Memory (MTArray x t)) (KMemptr \<lfloor>toploc m\<rfloor>) (k, env))" using s2 l_def m'_def 
      by (metis bind.bind_lunit snd_conv)
    then have "(k',env') = astack_dup a1 (Memory (MTArray x t)) (KMemptr \<lfloor>toploc m\<rfloor>) (k, env)" using 19 s2 m'_def l_def s2 by simp
    then have "k' = (let s = updateStore \<lfloor>toploc k\<rfloor> (KMemptr \<lfloor>toploc m\<rfloor>) k in snd (allocate s)) \<or> k' = k"
      unfolding astack_dup.simps push_def  by (auto split:option.splits)
    then have "\<forall>l. l \<noteq> \<lfloor>toploc k\<rfloor>  \<longrightarrow> accessStore l k' = accessStore l k" unfolding allocate_def updateStore_def accessStore_def by (auto split:option.splits)
      with 19 l_def m'_def show ?thesis unfolding allocate_def using assms astack_den_sub by (simp split:if_split_asm)
    qed
  next
    case False
    with 19 show ?thesis by simp
  qed
next
  case (20 x t p we wf wg wh c m k env)
 then have "(k', env') = astack_dup a1 (Memory (MTArray x t)) (KMemptr p) (k, env)" by  (simp split:if_split_asm)
  then have "k' = (let s = updateStore \<lfloor>toploc k\<rfloor> (KMemptr p) k in snd (allocate s)) \<or> k' = k"
      unfolding astack_dup.simps push_def  by (auto split:option.splits)
    then have "\<forall>l. l \<noteq> \<lfloor>toploc k\<rfloor>  \<longrightarrow> accessStore l k' = accessStore l k" unfolding allocate_def updateStore_def accessStore_def by (auto split:option.splits)
  then show ?thesis using astack_den_sub assms 20 by  (simp split:if_split_asm)
next
  case (21 x t p wi wj cd wk wl c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m)"
  obtain m'' where m'_def: "\<exists>x. (x, m'') = allocate m" unfolding allocate_def by simp
  then show ?thesis
  proof (cases "cpm2m p l x t cd m''")
    case None
    with 21 l_def m'_def show ?thesis unfolding allocate_def by  (simp split:if_split_asm)
  next
    case s2: (Some a)
    then have " wi = Calldata (MTArray x t) \<and> 0 < x\<and> denvalue env $$ a1 = None" using 21 
      by (metis option.discI)
    then have "Some (c', m', k', env') =
    cpm2m p \<lfloor>toploc m\<rfloor> x t cd (snd (allocate m)) \<bind> (\<lambda>m'. Some (c, m', astack_dup a1 (Memory (MTArray x t)) (KMemptr \<lfloor>toploc m\<rfloor>) (k, env)))" using 21 l_def  
      by simp
    then have "Some (c', m', k', env') = Some (c, a, astack_dup a1 (Memory (MTArray x t)) (KMemptr \<lfloor>toploc m\<rfloor>) (k, env))" using s2 l_def m'_def 
      by (metis bind.bind_lunit snd_conv)
    then have "(k',env') = astack_dup a1 (Memory (MTArray x t)) (KMemptr \<lfloor>toploc m\<rfloor>) (k, env)" using 21 s2 m'_def l_def s2 by simp
    then have "k' = (let s = updateStore \<lfloor>toploc k\<rfloor> (KMemptr \<lfloor>toploc m\<rfloor>) k in snd (allocate s)) \<or> k' = k"
      unfolding astack_dup.simps push_def  by (auto split:option.splits)
    then have "\<forall>l. l \<noteq> \<lfloor>toploc k\<rfloor>  \<longrightarrow> accessStore l k' = accessStore l k" unfolding allocate_def updateStore_def accessStore_def by (auto split:option.splits)

    with 21 l_def m'_def show ?thesis unfolding allocate_def using astack_den_sub assms by  (simp split:if_split_asm)
  qed
next
  case (22 x t p x' t' wm wn wo s c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m)"
  obtain m'' where m'_def: "\<exists>x. (x, m'') = allocate m" unfolding allocate_def by simp
  show ?thesis
  proof (cases "cps2m p l x' t' s m''")
    case None
    with 22 l_def m'_def show ?thesis unfolding allocate_def by (simp split:if_split_asm)
  next
    case s2: (Some a)
    
    then have "Some (c', m', k', env') = cps2m p l x' t' s m'' \<bind> (\<lambda>m''. Some (c, m'', astack_dup a1 (Memory (MTArray x t)) (KMemptr l) (k, env)))" using 22 m'_def l_def  
      
      by (metis (no_types, lifting) bind.bind_lunit option.discI snd_conv)
    
    then have "(k',env') = astack_dup a1 (Memory (MTArray x t)) (KMemptr l) (k, env)" using 22 s2 m'_def l_def s2 by simp
    then have "k' = (let s = updateStore \<lfloor>toploc k\<rfloor> (KMemptr l) k in snd (allocate s)) \<or> k' = k"
      unfolding astack_dup.simps push_def  by (auto split:option.splits)
    then have "\<forall>l. l \<noteq> \<lfloor>toploc k\<rfloor>  \<longrightarrow> accessStore l k' = accessStore l k" unfolding allocate_def updateStore_def accessStore_def by (auto split:option.splits)

    with 22 l_def m'_def show ?thesis unfolding allocate_def using  astack_den_sub assms by (simp split:if_split_asm)
  qed
next
  case (23 v wr ws wt wu wv ww)
  then show ?thesis by simp
next
  case (24 va v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (25 wq vc vb ws wt wu wv ww)
  then show ?thesis by simp
next
  case (26 v vc vb ws wt wu wv ww)
  then show ?thesis by simp
next
  case (27 v vc vb ws wt wu wv ww)
  then show ?thesis by simp
next
  case (28 wq vc v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (29 wq vc v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (30 wq vc v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (31 wq vc va vd ws wt wu wv ww)
  then show ?thesis by simp
next
  case (32 wq vc va ws wt wu wv ww)
  then show ?thesis by simp
next
  case (33 va v wt wu wv ww)
  then show ?thesis by simp
next
  case (34 wq vc vb wt wu wv ww)
  then show ?thesis by simp
next
  case (35 v vc vb wt wu wv ww)
  then show ?thesis by simp
next
  case (36 v vc vb wt wu wv ww)
  then show ?thesis by simp
next
  case (37 wq vc v wt wu wv ww)
  then show ?thesis by simp
next
  case (38 wq vc v wt wu wv ww)
  then show ?thesis by simp
next
  case (39 wq vc v wt wu wv ww)
  then show ?thesis by simp
next
  case (40 wq vc va vd wt wu wv ww)
  then show ?thesis by simp
next
  case (41 wq vc va wt wu wv ww)
  then show ?thesis by simp
next
  case (42 x t p wx wy wz xa xb c m k env)
  then have "(k', env') = astack_dup a1 (Storage (STArray x t)) (KStoptr p) (k, env)" by  (simp split:if_split_asm)
  then have "k' = (let s = updateStore \<lfloor>toploc k\<rfloor> (KStoptr p) k in snd (allocate s)) \<or> k' = k"
      unfolding astack_dup.simps push_def  by (auto split:option.splits)
    then have "\<forall>l. l \<noteq> \<lfloor>toploc k\<rfloor>  \<longrightarrow> accessStore l k' = accessStore l k" unfolding allocate_def updateStore_def accessStore_def by (auto split:option.splits)
  then show ?thesis using astack_den_sub assms 42 by (simp split:if_split_asm)
next
  case (43 t t' p xc xd xe xf xg c m k e)
 then have "(k', env') = astack_dup a1 (Storage (STMap t t')) (KStoptr p) (k, e)" by  (simp split:if_split_asm)
  then have "k' = (let s = updateStore \<lfloor>toploc k\<rfloor> (KStoptr p) k in snd (allocate s)) \<or> k' = k"
      unfolding astack_dup.simps push_def by (auto split:option.splits)
    then have "\<forall>l. l \<noteq> \<lfloor>toploc k\<rfloor>  \<longrightarrow> accessStore l k' = accessStore l k" unfolding allocate_def updateStore_def accessStore_def by (auto split:option.splits)
  then show ?thesis using astack_den_sub 43 assms by (simp split:if_split_asm)
next
  case (44 v va xk xl xm xn xo)
  then show ?thesis by simp
next
  case (45 v va ve vd xk xl xm xn xo)
  then show ?thesis by simp
next
  case (46 v va ve vd xk xl xm xn xo)
  then show ?thesis by simp
next
  case (47 v va ve vd xk xl xm xn xo)
  then show ?thesis by simp
next
  case (48 v xj xk xl xm xn xo)
  then show ?thesis by simp
next
  case (49 xi xk xl xm xn xo)
  then show ?thesis by simp
next
  case (50 xi vc vb xk xl xm xn xo)
  then show ?thesis by simp
next
  case (51 xi vc vb xk xl xm xn xo)
  then show ?thesis by simp
next
  case (52 xi vc vb xk xl xm xn xo)
  then show ?thesis by simp
qed


lemma decl_KValue_tp_match:
  assumes "decl i tp (Some (a1, Value t)) cp cd mem sto (c, m, k, env) = Some (c', m', k', env')"
  shows "\<exists>vv. tp = Value vv" by(cases rule:decl.elims[OF assms(1)], simp+)

lemma decl_Calldata_tp_match:
  assumes "decl i tp (Some (a1, Calldata t)) cp cd mem sto (c, m, k, env) = Some (c', m', k', env')"
  shows "\<exists>vv. tp = Calldata vv \<or> tp = Memory vv" by(cases rule:decl.elims[OF assms(1)], simp+)

lemma decl_Memory_tp_match:
  assumes "decl i tp (Some (a1, Memory t)) cp cd mem sto (c, m, k, env) = Some (c', m', k', env')"
  shows "\<exists>vv. tp = Calldata vv \<or> tp = Memory vv" by (cases rule:decl.elims[OF assms(1)], simp+)

lemma decl_Memory_tp_options:
  assumes "decl i tp (Some (a1, Storage t)) cp cd mem sto (c, m, k, env) = Some (c', m', k', env')"
  shows "(\<exists>x t' t''. t = STArray x t' \<and> cps2mTypeCompatible (STArray x t') (MTArray x t'') \<and> tp = Memory (MTArray x t''))  \<or> tp = Storage t" 
proof (cases rule:decl.elims[OF assms(1)])
  case (1 i t uu uv uw ux c m k e)
  then show ?thesis by simp
next
  case (2 i t v t' uy uz va vb c m k e)
  then show ?thesis by simp
next
  case (3 vc vd ve vb vf vg vh vi vj)
  then show ?thesis by simp
next
  case (4 vc vd ve vb vf vg vh vi vj)
  then show ?thesis by simp
next
  case (5 vc vd ve vb vf vg vh vi vj)
  then show ?thesis by simp
next
  case (6 vc vd va ve vf vg vh vi vj)
  then show ?thesis by simp
next
  case (7 vc vd va ve vf vg vh vi vj)
  then show ?thesis by simp
next
  case (8 vc vd va ve vf vg vh vi vj)
  then show ?thesis by simp
next
  case (9 i x t p t' cd vk vl c m k e)
  then show ?thesis by auto
next
  case (10 i x t p t' vm mem vn c m k e)
  then show ?thesis by auto
next
  case (11 i v vp vq vr vs vt vu)
  then show ?thesis by simp
next
  case (12 i vo vq vr vs vt vu)
  then show ?thesis by simp
next
  case (13 i vo vc vb vq vr vs vt vu)
  then show ?thesis by simp
next
  case (14 i v vc vb vq vr vs vt vu)
  then show ?thesis by simp
next
  case (15 i vo vc vb vr vs vt vu)
  then show ?thesis by simp
next
  case (16 i vo vc vb vq vr vs vt vu)
  then show ?thesis by simp
next
  case (17 i vo vp vr vs vt vu)
  then show ?thesis by simp
next
  case (18 i x t vv vw vx vy c m k e)
  then show ?thesis by simp
next
  case (19 i x t p t' vz mem wa c m k e)
  then show ?thesis by auto
next
  case (20 i x t p t' wb wc wd c m k e)
  then show ?thesis by auto
next
  case (21 i x t p t' we cd wf wg c m k e)
  then show ?thesis by auto
next
  case (22 i x t p x' t' wh wi wj s c m k e)
  then have "cps2mTypeCompatible (STArray x' t') (MTArray x t)"
    by (auto split:if_splits)
  then show ?thesis using 22(2,3) by auto
next
  case (23 wk v wm wn wo wp wq wr)
  then show ?thesis by simp
next
  case (24 wk va v wn wo wp wq wr)
  then show ?thesis by simp
next
  case (25 wk wl vc vb wn wo wp wq wr)
  then show ?thesis by simp
next
  case (26 wk v vc vb wn wo wp wq wr)
  then show ?thesis by simp
next
  case (27 wk v vc vb wn wo wp wq wr)
  then show ?thesis by simp
next
  case (28 wk wl vc v wn wo wp wq wr)
  then show ?thesis by simp
next
  case (29 wk wl vc v wn wo wp wq wr)
  then show ?thesis by simp
next
  case (30 wk wl vc v wn wo wp wq wr)
  then show ?thesis by simp
next
  case (31 wk wl vc va vd wn wo wp wq wr)
  then show ?thesis by simp
next
  case (32 wk wl vc va wn wo wp wq wr)
  then show ?thesis by simp
next
  case (33 wk va v wo wp wq wr)
  then show ?thesis by simp
next
  case (34 wk wl vc vb wo wp wq wr)
  then show ?thesis by simp
next
  case (35 wk v vc vb wo wp wq wr)
  then show ?thesis by simp
next
  case (36 wk v vc vb wo wp wq wr)
  then show ?thesis by simp
next
  case (37 wk wl vc v wo wp wq wr)
  then show ?thesis by simp
next
  case (38 wk wl vc v wo wp wq wr)
  then show ?thesis by simp
next
  case (39 wk wl vc v wo wp wq wr)
  then show ?thesis by simp
next
  case (40 wk wl vc va vd wo wp wq wr)
  then show ?thesis by simp
next
  case (41 wk wl vc va wo wp wq wr)
  then show ?thesis by simp
next
  case (42 i x t p t' ws wt wu wv c m k e)
  then show ?thesis by (simp split:if_split_asm)
next
  case (43 i t t' p t'' ww wx wy wz c m k e)
  then show ?thesis by (simp split:if_split_asm)
next
  case (44 xa v va xd xe xf xg xh)
  then show ?thesis by simp
next
  case (45 xa v va ve vd xd xe xf xg xh)
  then show ?thesis by simp
next
  case (46 xa v va ve vd xd xe xf xg xh)
  then show ?thesis by simp
next
  case (47 xa v va ve vd xd xe xf xg xh)
  then show ?thesis by simp
next
  case (48 xa v xc xd xe xf xg xh)
  then show ?thesis by simp
next
  case (49 xa xb xd xe xf xg xh)
  then show ?thesis by simp
next
  case (50 xa xb vc vb xd xe xf xg xh)
  then show ?thesis by simp
next
  case (51 xa xb vc vb xd xe xf xg xh)
  then show ?thesis by simp
next
  case (52 xa xb vc vb xd xe xf xg xh)
  then show ?thesis by simp
qed

lemma decl_StorageStack_options:
  assumes "decl i tp a1 cp cd mem sto (c, m, k, env) = Some (c', m', k', env')"
    and "\<forall>x. tp \<noteq> Storage x"
    and "(denvalue env') $$ ip' = Some ((Storage t, Stackloc l))"
    and "accessStore l k' = Some (KStoptr ptr)"
  shows "accessStore l k = accessStore l k'" 
proof (cases rule:decl.elims[OF assms(1)])
  case (1 i t uu uv uw ux c m k e)
  then have dv:"(denvalue env') $$ ip' = (denvalue env) $$ ip'" using assms unfolding astack_dup.simps updateEnv.simps 
    using decl_env decl_env_storage by (auto split:option.splits if_splits)
  have pd:"(k', env') = astack_dup i (Value t) (KValue (ival t)) (k, e)" using 1 by simp
  then have k'D:"k' = k \<or> k' = push (KValue (ival t)) k" unfolding astack_dup.simps by (auto split:option.splits)
  have e'D:"env' = updateEnv i (Value t) (Stackloc \<lfloor>toploc k\<rfloor>) e \<or> env' = e" using pd unfolding astack_dup.simps 
    by (metis option.case_eq_if snd_conv)
  then show ?thesis 
  proof(cases "denvalue e $$ i")
    case None
    then have k'Def:"k' = push (KValue (ival t)) k \<and> env' = updateEnv i (Value t) (Stackloc \<lfloor>toploc k\<rfloor>) e"
      using pd unfolding astack_dup.simps by simp
    then have "l \<noteq> \<lfloor>toploc k\<rfloor>" using assms(4) unfolding push_def allocate_def updateStore_def accessStore_def by auto
    then show ?thesis using k'Def unfolding push_def allocate_def updateStore_def accessStore_def  
      using "1"(8) by auto 
  next
    case (Some a)
    then have "k' = k \<and> e = env'" using pd unfolding astack_dup.simps by simp
    then show ?thesis using 1 by simp
  qed
next
  case (2 i t v t' uy uz va vb c m k e)
  
  obtain v' where v'Def:"convert t' t v = Some v'" using 2 by fastforce
  
  then show ?thesis 
  proof(cases "denvalue e $$ i")
    case None
    then have "(k', env') = ((push (KValue v') k, updateEnv i (Value t) (Stackloc \<lfloor>toploc k\<rfloor>) e))"
      using assms 2 v'Def unfolding astack_dup.simps  by (auto split:option.splits)
    then have "l \<noteq> \<lfloor>toploc k\<rfloor>" using assms(4) unfolding push_def updateStore_def accessStore_def allocate_def by auto
    then have "accessStore l k' = accessStore l k" using 2(9)
      unfolding push_def updateStore_def accessStore_def allocate_def astack.simps using v'Def 
      by (metis "2"(8) accessStore_def assms(1) decl_stack_change)
    then show ?thesis using "2"(8) by auto
  next
    case (Some a)
    then have "k' = k \<and> env' = e"
      using 2 assms unfolding astack_dup.simps using v'Def by auto
    then show ?thesis  using assms 2 by blast
  qed
next
  case (3 vc vd ve vb vf vg vh vi vj)
  then show ?thesis by simp
next
  case (4 vc vd ve vb vf vg vh vi vj)
  then show ?thesis by simp
next
  case (5 vc vd ve vb vf vg vh vi vj)
  then show ?thesis by simp
next
  case (6 vc vd va ve vf vg vh vi vj)
  then show ?thesis by simp
next
  case (7 vc vd va ve vf vg vh vi vj)
  then show ?thesis by simp
next
  case (8 vc vd va ve vf vg vh vi vj)
  then show ?thesis by simp
next
  case (9 i x t p t' cd vk vl c m k e)
  obtain l' where v'Def:"l' = \<lfloor>toploc c\<rfloor>" using 9 by fastforce

  have a1:"t' = Calldata (MTArray x t) \<and> 0 < x" using 9 by (auto split:if_splits)
  then obtain c'' uu where c'Def:"(uu, c'') = allocate c" using 9 
    by (simp add: allocate_def)
  then obtain c''' where a2:"cpm2m p l' x t cd c'' = Some c'''" using 9  v'Def a1 
    by (metis (no_types, lifting) bind.bind_lzero case_prod_conv not_None_eq)
  then show ?thesis
  proof(cases "denvalue e $$ i")
    case None
    then have a3:"Some (c', m', k', env') = Some (c''', m, astack_dup i (Calldata (MTArray x t)) (KCDptr l') (k, e))" 
      using 9 a2 c'Def a1 v'Def 
      by (metis (mono_tags, lifting) bind.bind_lunit case_prod_conv)
    then have kNew:"(k', env') = (push (KCDptr l') k, updateEnv i (Calldata (MTArray x t)) (Stackloc \<lfloor>toploc k\<rfloor>) e)" 
      unfolding astack_dup.simps using None by auto
    then have "l \<noteq> \<lfloor>toploc k\<rfloor>" using assms(4) v'Def unfolding push_def updateStore_def accessStore_def allocate_def by auto
    then have "accessStore l k' = accessStore l k" using 9(9) kNew
      unfolding push_def updateStore_def accessStore_def allocate_def astack.simps using v'Def by auto
    then show ?thesis using 9 by simp
  next
    case (Some a)
    then have "k' = k \<and> e = env'" using 9 a1 c'Def a2 v'Def unfolding astack_dup.simps allocate_def by (auto split:if_splits option.splits)
    then show ?thesis using 9 assms by blast
  qed
next
  case (10 i x t p t' vm mem vn c m k e)
  obtain l' where v'Def:"l' = \<lfloor>toploc c\<rfloor>" using 10 by fastforce
  then have "(k', env') = (k',env')"
    using assms 10 unfolding astack.simps by simp
  have a1:"t' = Memory (MTArray x t) \<and> 0 < x" using 10 by (auto split:if_splits)
  then obtain c'' uu where c'Def:"(uu, c'') = allocate c" using 10 
    by (simp add: allocate_def)
  then obtain c''' where a2:"cpm2m p l' x t mem c'' = Some c'''" using 10 v'Def a1 
    by (metis (no_types, lifting) bind.bind_lzero case_prod_conv not_None_eq)
  then show ?thesis
  proof(cases "denvalue e $$ i")
    case None
    then have a3:"Some (c', m', k', env') = Some (c''', m, astack_dup i (Calldata (MTArray x t)) (KCDptr l') (k, e))" 
      using 10 a2 c'Def a1 v'Def 
      by (metis (mono_tags, lifting) bind.bind_lunit case_prod_conv)
    then have kNew:"(k', env') = (push (KCDptr l') k, updateEnv i (Calldata (MTArray x t)) (Stackloc \<lfloor>toploc k\<rfloor>) e)" 
      unfolding astack_dup.simps using None by auto
    then have "l \<noteq> \<lfloor>toploc k\<rfloor>" using assms(4) v'Def unfolding push_def updateStore_def accessStore_def allocate_def by auto
    then have "accessStore l k' = accessStore l k" using 10(9) kNew
      unfolding push_def updateStore_def accessStore_def allocate_def astack.simps using v'Def by auto
    then show ?thesis using 10 by simp
  next
    case (Some a)
    then have "k' = k \<and> e = env'" using 10 a1 c'Def a2 v'Def unfolding astack_dup.simps allocate_def by (auto split:if_splits option.splits)
    then show ?thesis using 10 assms by blast
  qed
next
  case (11 i v vp vq vr vs vt vu)
  then show ?thesis by simp
next
  case (12 i vo vq vr vs vt vu)
  then show ?thesis by simp
next
  case (13 i vo vc vb vq vr vs vt vu)
  then show ?thesis by simp
next
  case (14 i v vc vb vq vr vs vt vu)
  then show ?thesis by simp
next
  case (15 i vo vc vb vr vs vt vu)
  then show ?thesis by simp
next
  case (16 i vo vc vb vq vr vs vt vu)
  then show ?thesis by simp
next
  case (17 i vo vp vr vs vt vu)
  then show ?thesis by simp
next
  case (18 i x t vv vw vx vy c m k e)
  obtain m' where a1:"m' = minit x t m" using 18 by simp
  
  then show ?thesis 
  proof(cases "denvalue e $$ i")
    case None
    then have " Some (c', m', k', env') = Some (c, m',  push (KMemptr \<lfloor>toploc m\<rfloor>) k, updateEnv i (Memory (MTArray x t)) (Stackloc \<lfloor>toploc k\<rfloor>) e)"
      using 18 unfolding astack.simps by (auto split:option.splits if_splits)
    then have "l \<noteq> \<lfloor>toploc k\<rfloor>" using assms(4) unfolding push_def updateStore_def accessStore_def allocate_def by auto
    then have "accessStore l k' = accessStore l k" using 18(9) None unfolding push_def updateStore_def accessStore_def allocate_def astack.simps  
      by (metis accessStore_def decl.simps(18) decl_stack_change)
    then show ?thesis using 18 by simp
  next
    case (Some a)
    then have "k' = k \<and> env' = e" using 18 by simp
    then show ?thesis using 18 by blast
  qed
next
  case (19 i x t p t' vz mem wa c m k e)
  have a1:"t' = Memory (MTArray x t) \<and> 0 < x\<and> denvalue e $$ i = None" using 19 by (auto split:if_splits)
  then obtain c''' where a2:"cpm2m p \<lfloor>toploc m\<rfloor> x t mem (snd (allocate m)) = Some c'''" using 19  a1 by fastforce
  
  then show ?thesis 
  proof(cases "denvalue e $$ i")
    case None
    then have a3:"Some (c', m', k', env') = Some (c, c''',  astack i (Memory (MTArray x t)) (KMemptr \<lfloor>toploc m\<rfloor>) (k, e))" 
      using 19 a2 a1 by auto 
    then have kNew:"(k', env') = ( push (KMemptr \<lfloor>toploc m\<rfloor>) k, updateEnv i (Memory (MTArray x t)) (Stackloc \<lfloor>toploc k\<rfloor>) e)" unfolding astack.simps by auto
    then have "l \<noteq> \<lfloor>toploc k\<rfloor>" using assms(4) unfolding push_def updateStore_def accessStore_def allocate_def by auto
    then have "accessStore l k' = accessStore l k" using 19(9) kNew
      unfolding push_def updateStore_def accessStore_def allocate_def astack.simps by auto
    then show ?thesis using 19 by simp
  next
    case (Some a)
    then have "k' = k \<and> env' = e" using 19 a1 a2 unfolding astack_dup.simps by simp

    then show ?thesis using 19 by blast
  qed
next
  case (20 i x t p t' wb wc wd c m k e)
  then have a1:"Some (c', m', k', env') = Some (c, m, astack_dup i (Memory (MTArray x t)) (KMemptr p) (k, e))" using 20
    by (simp split:if_splits)
  then show ?thesis 
  proof(cases "denvalue e $$ i")
    case None
    then have kNew:"(k', env') = (push (KMemptr p) k, updateEnv i (Memory (MTArray x t)) (Stackloc \<lfloor>toploc k\<rfloor>) e)" 
      using a1 unfolding astack_dup.simps by auto
    then have "l \<noteq> \<lfloor>toploc k\<rfloor>" using assms(4) unfolding push_def updateStore_def accessStore_def allocate_def by auto
    then have "accessStore l k' = accessStore l k" using 20(9) kNew
      unfolding push_def updateStore_def accessStore_def allocate_def astack.simps by auto  
    then show ?thesis using 20 by auto
  next
    case (Some a)
    then have "k' = k" using a1 by simp
    then show ?thesis using 20 by blast
  qed
next
  case (21 i x t p t' we cd wf wg c m k e)
  
  have a1:"t' = Calldata (MTArray x t) \<and> 0 < x\<and> denvalue e $$ i = None" using 21 by (auto split:if_splits)
  then obtain c''' where a2:"cpm2m p \<lfloor>toploc m\<rfloor> x t cd (snd (allocate m)) = Some c'''" using 21  a1 by fastforce
  then have a3:"Some (c', m', k', env') = Some (c, c''',  astack_dup i (Memory (MTArray x t)) (KMemptr \<lfloor>toploc m\<rfloor>) (k, e))" 
    using 21 a2 a1 by auto 
  then show ?thesis 
  proof(cases "denvalue e $$ i")
    case None
    then have kNew:"(k', env') = ( push (KMemptr \<lfloor>toploc m\<rfloor>) k, updateEnv i (Memory (MTArray x t)) (Stackloc \<lfloor>toploc k\<rfloor>) e)" 
      using a3 unfolding astack_dup.simps by auto
    then have "l \<noteq> \<lfloor>toploc k\<rfloor>" using assms(4) unfolding push_def updateStore_def accessStore_def allocate_def by auto
    then have "accessStore l k' = accessStore l k" using 21(9) kNew
      unfolding push_def updateStore_def accessStore_def allocate_def astack.simps by auto
    then show ?thesis using 21 by simp
  next
    case (Some a)
    then have "k' = k" using a3 by auto
    then show ?thesis using 21 by blast
  qed
next
  case (22 i x t p x' t' wh wi wj s c m k e)
  then have a1:"cps2mTypeCompatible (STArray x' t') (MTArray x t)\<and> denvalue e $$ i = None" using 22
    by (auto split:if_splits)
  then obtain c''' where a2:"cps2m p \<lfloor>toploc m\<rfloor> x' t' s (snd (allocate m)) = Some c'''" using 22  by fastforce
  then have a3:"Some (c', m', k', env') = Some (c, c''',  astack_dup i (Memory (MTArray x t)) (KMemptr \<lfloor>toploc m\<rfloor>) (k, e))" 
    using 22 a2 a1  by auto 
  then show ?thesis 
  proof(cases "denvalue e $$ i")
    case None
    then have kNew:"(k', env') = ( push (KMemptr \<lfloor>toploc m\<rfloor>) k, updateEnv i (Memory (MTArray x t)) (Stackloc \<lfloor>toploc k\<rfloor>) e)" 
      using a3 unfolding astack_dup.simps by auto
    then have "l \<noteq> \<lfloor>toploc k\<rfloor>" using assms(4) unfolding push_def updateStore_def accessStore_def allocate_def by auto
    then have "accessStore l k' = accessStore l k" using 22(9) kNew
      unfolding push_def updateStore_def accessStore_def allocate_def astack.simps by auto
    then show ?thesis using 22 by simp
  next
    case (Some a)
    then have "k' = k" using a3 by auto
    then show ?thesis using 22 by blast
  qed
next
  case (23 wk v wm wn wo wp wq wr)
  then show ?thesis by simp
next
  case (24 wk va v wn wo wp wq wr)
  then show ?thesis by simp
next
  case (25 wk wl vc vb wn wo wp wq wr)
  then show ?thesis by simp
next
  case (26 wk v vc vb wn wo wp wq wr)
  then show ?thesis by simp
next
  case (27 wk v vc vb wn wo wp wq wr)
  then show ?thesis by simp
next
  case (28 wk wl vc v wn wo wp wq wr)
  then show ?thesis by simp
next
  case (29 wk wl vc v wn wo wp wq wr)
  then show ?thesis by simp
next
  case (30 wk wl vc v wn wo wp wq wr)
  then show ?thesis by simp
next
  case (31 wk wl vc va vd wn wo wp wq wr)
  then show ?thesis by simp
next
  case (32 wk wl vc va wn wo wp wq wr)
  then show ?thesis by simp
next
  case (33 wk va v wo wp wq wr)
  then show ?thesis by simp
next
  case (34 wk wl vc vb wo wp wq wr)
  then show ?thesis by simp
next
  case (35 wk v vc vb wo wp wq wr)
  then show ?thesis by simp
next
  case (36 wk v vc vb wo wp wq wr)
  then show ?thesis by simp
next
  case (37 wk wl vc v wo wp wq wr)
  then show ?thesis by simp
next
  case (38 wk wl vc v wo wp wq wr)
  then show ?thesis by simp
next
  case (39 wk wl vc v wo wp wq wr)
  then show ?thesis by simp
next
  case (40 wk wl vc va vd wo wp wq wr)
  then show ?thesis by simp
next
  case (41 wk wl vc va wo wp wq wr)
  then show ?thesis by simp
next
  case (42 i x t p t' ws wt wu wv c m k e)
  then show ?thesis using decl_env_storage assms unfolding astack.simps push_def allocate_def accessStore_def updateStore_def by blast
next
  case (43 i t t' p t'' ww wx wy wz c m k e)
  then show ?thesis using decl_env_storage assms unfolding astack.simps push_def allocate_def accessStore_def updateStore_def by blast
next
  case (44 xa v va xd xe xf xg xh)
  then show ?thesis by simp
next
  case (45 xa v va ve vd xd xe xf xg xh)
  then show ?thesis by simp
next
  case (46 xa v va ve vd xd xe xf xg xh)
  then show ?thesis by simp
next
  case (47 xa v va ve vd xd xe xf xg xh)
  then show ?thesis by simp
next
  case (48 xa v xc xd xe xf xg xh)
  then show ?thesis by simp
next
  case (49 xa xb xd xe xf xg xh)
  then show ?thesis by simp
next
  case (50 xa xb vc vb xd xe xf xg xh)
  then show ?thesis by simp
next
  case (51 xa xb vc vb xd xe xf xg xh)
  then show ?thesis by simp
next
  case (52 xa xb vc vb xd xe xf xg xh)
  then show ?thesis by simp
qed

lemma decl_env_storlocs_unchanged:
  assumes "decl i tp a3 cp cd mem sto (c, m, k, env) = Some (c', m', k', env')"
  shows "\<forall>t l. denvalue env' $$ i = Some (t, Storeloc l) \<longrightarrow> denvalue env $$ i = Some (t, Storeloc l)"
  using assms
proof (cases rule:decl.elims)
  case (1 t uu uv uw ux c m k env)
  then show ?thesis by (auto split:option.splits)
next
  case (2 t v t' uy uz va vb c m k e)
  show ?thesis
  proof (cases "convert t' t v")
    case None
    with 2 show ?thesis by simp
  next
    case s: (Some a)
    with 2 s show ?thesis by (auto split:option.splits)
  qed
next
  case (3 vd ve vb vf vg vh vi vj)
  then show ?thesis by simp
next
  case (4 vd ve vb vf vg vh vi vj)
  then show ?thesis by simp
next
  case (5 vd ve vb vf vg vh vi vj)
  then show ?thesis by simp
next
  case (6 vd va ve vf vg vh vi vj)
  then show ?thesis by simp
next
  case (7 vd va ve vf vg vh vi vj)
  then show ?thesis by simp
next
  case (8 vd va ve vf vg vh vi vj)
  then show ?thesis by simp
next
  case (9 x t p vk cd vl vm c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc c)"
  obtain c' where c_def: "\<exists>x. (x, c') = allocate c" unfolding allocate_def by simp
  show ?thesis
  proof (cases "cpm2m p l x t cd c'")
    case None
    with 9 l_def c_def show ?thesis unfolding allocate_def by (simp split:if_split_asm)
  next
    case s2: (Some a)
    with 9 l_def c_def show ?thesis unfolding allocate_def using astack_den_sub by (simp split:if_split_asm option.splits)
  qed
next
  case (10 x t p vn vo mem vp c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc c)"
  obtain c' where c_def: "\<exists>x. (x, c') = allocate c" unfolding allocate_def by simp
  show ?thesis
  proof (cases "cpm2m p l x t mem c'")
    case None
    with 10 l_def c_def show ?thesis unfolding allocate_def by (simp split:if_split_asm)
  next
    case s2: (Some a)
    with 10 l_def c_def show ?thesis unfolding allocate_def using astack_den_sub by (simp split:if_split_asm option.splits)
  qed
next
  case (11 v vr vs vt vu vv vw)
  then show ?thesis by simp
next
  case (12 vq vs vt vu vv vw)
  then show ?thesis by simp
next
  case (13 vq vc vb vs vt vu vv vw)
  then show ?thesis by simp
next
  case (14 v vc vb vs vt vu vv vw)
  then show ?thesis by simp
next
  case (15 vq vc vb vt vu vv vw)
  then show ?thesis by simp
next
  case (16 vq vc vb vs vt vu vv vw)
  then show ?thesis by simp
next
  case (17 vq vr vt vu vv vw)
  then show ?thesis by simp
next
  case (18 x t vx vy vz wa c m k env)
  then show ?thesis using astack_den_sub by (simp split:if_split_asm option.splits)
next
  case (19 x t p wb wc mem wd c m k env)
  show ?thesis
  proof (cases cp)
    case True
    define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m)"
    obtain m' where m'_def: "\<exists>x. (x, m') = allocate m" unfolding allocate_def by simp
    then show ?thesis
    proof (cases "cpm2m p l x t mem m'")
      case None
      with 19 l_def m'_def show ?thesis unfolding allocate_def by (simp split:if_split_asm)
    next
      case s2: (Some a)
      with 19 l_def m'_def show ?thesis unfolding allocate_def using astack_den_sub by (simp split:if_split_asm option.splits)
    qed
  next
    case False
    with 19 show ?thesis by simp
  qed
next
  case (20 x t p we wf wg wh c m k env)
  then show ?thesis using astack_den_sub by  (simp split:if_split_asm option.splits)
next
  case (21 x t p wi wj cd wk wl c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m)"
  obtain m' where m'_def: "\<exists>x. (x, m') = allocate m" unfolding allocate_def by simp
  then show ?thesis
  proof (cases "cpm2m p l x t cd m'")
    case None
    with 21 l_def m'_def show ?thesis unfolding allocate_def by  (simp split:if_split_asm)
  next
    case s2: (Some a)
    with 21 l_def m'_def show ?thesis unfolding allocate_def using astack_den_sub by  (simp split:if_split_asm option.splits)
  qed
next
  case (22 x t p x' t' wm wn wo s c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m)"
  obtain m' where m'_def: "\<exists>x. (x, m') = allocate m" unfolding allocate_def by simp
  show ?thesis
  proof (cases "cps2m p l x' t' s m'")
    case None
    with 22 l_def m'_def show ?thesis unfolding allocate_def by (simp split:if_split_asm)
  next
    case s2: (Some a)
    with 22 l_def m'_def show ?thesis unfolding allocate_def using  astack_den_sub by (simp split:if_split_asm option.splits)
  qed
next
  case (23 v wr ws wt wu wv ww)
  then show ?thesis by simp
next
  case (24 va v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (25 wq vc vb ws wt wu wv ww)
  then show ?thesis by simp
next
  case (26 v vc vb ws wt wu wv ww)
  then show ?thesis by simp
next
  case (27 v vc vb ws wt wu wv ww)
  then show ?thesis by simp
next
  case (28 wq vc v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (29 wq vc v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (30 wq vc v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (31 wq vc va vd ws wt wu wv ww)
  then show ?thesis by simp
next
  case (32 wq vc va ws wt wu wv ww)
  then show ?thesis by simp
next
  case (33 va v wt wu wv ww)
  then show ?thesis by simp
next
  case (34 wq vc vb wt wu wv ww)
  then show ?thesis by simp
next
  case (35 v vc vb wt wu wv ww)
  then show ?thesis by simp
next
  case (36 v vc vb wt wu wv ww)
  then show ?thesis by simp
next
  case (37 wq vc v wt wu wv ww)
  then show ?thesis by simp
next
  case (38 wq vc v wt wu wv ww)
  then show ?thesis by simp
next
  case (39 wq vc v wt wu wv ww)
  then show ?thesis by simp
next
  case (40 wq vc va vd wt wu wv ww)
  then show ?thesis by simp
next
  case (41 wq vc va wt wu wv ww)
  then show ?thesis by simp
next
  case (42 x t p wx wy wz xa xb c m k env)
  then show ?thesis using astack_den_sub assms by (simp split:if_split_asm option.splits)
next
  case (43 t t' p xc xd xe xf xg c m k e)
  then show ?thesis using astack_den_sub assms by (simp split:if_split_asm option.splits)
next
  case (44 v va xk xl xm xn xo)
  then show ?thesis by simp
next
  case (45 v va ve vd xk xl xm xn xo)
  then show ?thesis by simp
next
  case (46 v va ve vd xk xl xm xn xo)
  then show ?thesis by simp
next
  case (47 v va ve vd xk xl xm xn xo)
  then show ?thesis by simp
next
  case (48 v xj xk xl xm xn xo)
  then show ?thesis by simp
next
  case (49 xi xk xl xm xn xo)
  then show ?thesis by simp
next
  case (50 xi vc vb xk xl xm xn xo)
  then show ?thesis by simp
next
  case (51 xi vc vb xk xl xm xn xo)
  then show ?thesis by simp
next
  case (52 xi vc vb xk xl xm xn xo)
  then show ?thesis by simp
qed

lemma decl_env_monotonic:
  assumes "decl i tp a3 cp cd mem sto (c, m, k, env) = Some (c', m', k', env')"
    and " denvalue env $$ ii = Some x"
  shows "denvalue env' $$ ii = Some x"
  using assms
proof (cases rule:decl.elims)
  case (1 t uu uv uw ux c m k env)
  then show ?thesis using assms by (auto split:option.splits)
next
  case (2 t v t' uy uz va vb c m k e)
  show ?thesis
  proof (cases "convert t' t v")
    case None
    with 2 show ?thesis by simp
  next
    case s: (Some a)
    with 2 s show ?thesis using assms by (auto split:option.splits)
  qed
next
  case (3 vd ve vb vf vg vh vi vj)
  then show ?thesis by simp
next
  case (4 vd ve vb vf vg vh vi vj)
  then show ?thesis by simp
next
  case (5 vd ve vb vf vg vh vi vj)
  then show ?thesis by simp
next
  case (6 vd va ve vf vg vh vi vj)
  then show ?thesis by simp
next
  case (7 vd va ve vf vg vh vi vj)
  then show ?thesis by simp
next
  case (8 vd va ve vf vg vh vi vj)
  then show ?thesis by simp
next
  case (9 x t p vk cd vl vm c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc c)"
  obtain c''' where c_def: "\<exists>x. (x, c''') = allocate c" unfolding allocate_def by simp
  have vkl:" vk = Calldata (MTArray x t) \<and> 0 < x\<and> denvalue env $$ i = None" using 9 by (simp split:if_split_asm)
  show ?thesis
  proof (cases "cpm2m p l x t cd c'''")
    case None
    with 9 l_def c_def show ?thesis unfolding allocate_def by (simp split:if_split_asm)
  next
    case s2: (Some a)
    then have endc:"(c', m', k', env') = (a, m, astack_dup i (Calldata (MTArray x t)) (KCDptr l) (k, env))"
      using 9 l_def c_def vkl 
      by (metis (mono_tags, lifting) bind.bind_lunit case_prod_conv option.inject)
    show ?thesis 
    proof(cases "i = ii")
      case True
      with 9 endc show ?thesis using assms unfolding allocate_def astack_dup.simps by auto
    next
      case False
      then have "denvalue env $$ ii = denvalue env' $$ ii" 
        using endc assms unfolding allocate_def astack_dup.simps updateEnv.simps allocate_def by (simp split:if_split_asm option.splits)
      with 9 l_def c_def show ?thesis using assms unfolding allocate_def astack_dup.simps  by (simp split:if_split_asm option.splits)
    qed
       
  qed
next
  case (10 x t p vn vo mem vp c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc c)"
  obtain c''' where c_def: "\<exists>x. (x, c''') = allocate c" unfolding allocate_def by simp
  have vkl:"vn = Memory (MTArray x t) \<and> 0 < x\<and> denvalue env $$ i = None" using 10 by (simp split:if_split_asm)
  show ?thesis
  proof (cases "cpm2m p l x t mem c'''")
    case None
    with 10 l_def c_def show ?thesis unfolding allocate_def by (simp split:if_split_asm)
  next
    case s2: (Some a)
    then have endc:"(c', m', k', env') = (a, m, astack_dup i (Calldata (MTArray x t)) (KCDptr l) (k, env))"
      using 10 l_def c_def vkl 
      by (metis (mono_tags, lifting) bind.bind_lunit case_prod_conv option.inject)
    show ?thesis
    proof(cases "i = ii")
      case True
      with 10 endc show ?thesis using assms unfolding allocate_def astack_dup.simps by auto
    next
      case False
      then have "denvalue env $$ ii = denvalue env' $$ ii" 
        using endc assms unfolding allocate_def astack_dup.simps updateEnv.simps allocate_def by (simp split:if_split_asm option.splits)
      with 10 l_def c_def show ?thesis using assms unfolding allocate_def astack_dup.simps  by (simp split:if_split_asm option.splits)
    qed
  qed
next
  case (11 v vr vs vt vu vv vw)
  then show ?thesis by simp
next
  case (12 vq vs vt vu vv vw)
  then show ?thesis by simp
next
  case (13 vq vc vb vs vt vu vv vw)
  then show ?thesis by simp
next
  case (14 v vc vb vs vt vu vv vw)
  then show ?thesis by simp
next
  case (15 vq vc vb vt vu vv vw)
  then show ?thesis by simp
next
  case (16 vq vc vb vs vt vu vv vw)
  then show ?thesis by simp
next
  case (17 vq vr vt vu vv vw)
  then show ?thesis by simp
next
  case (18 x t vx vy vz wa c m k env)
  then show ?thesis 
  proof(cases " i = ii")
    case True
    then show ?thesis using 18 assms unfolding  astack_dup.simps updateEnv.simps by (simp split:if_split_asm option.splits)
  next
    case False
    then show ?thesis using 18 assms unfolding  astack_dup.simps updateEnv.simps by (simp split:if_split_asm option.splits)
  qed
next
  case (19 x t p wb wc mem wd c m k env)
  show ?thesis
  proof (cases cp)
    case True
    define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m)"
    obtain m'' where m'_def: "\<exists>x. (x, m'') = allocate m" unfolding allocate_def by simp
    have vkl:"wb = Memory (MTArray x t) \<and> 0 < x\<and>denvalue env $$ i = None" using 19 by (simp split:if_split_asm)
    then show ?thesis
    proof (cases "cpm2m p l x t mem m''")
      case None
      with 19 l_def m'_def show ?thesis unfolding allocate_def by (simp split:if_split_asm)
    next
      case s2: (Some a)
      then have cc:"(c', m', k', env') = (c, a, astack_dup i (Memory (MTArray x t)) (KMemptr \<lfloor>toploc m\<rfloor>) (k, env))"
        using 19 assms l_def vkl m'_def unfolding allocate_def by simp
      then show ?thesis 
      proof(cases "i=ii")
        case True
        then show ?thesis using assms cc 19 unfolding allocate_def astack_dup.simps updateEnv.simps by simp

      next
        case False
        then show ?thesis using assms cc 19 unfolding allocate_def astack_dup.simps updateEnv.simps by (simp split:if_split_asm option.splits)
      qed  
        
    qed
  next
    case False
    with 19 show ?thesis by simp
  qed
next
  case (20 x t p we wf wg wh c m k env)
  then show ?thesis
  proof(cases " i = ii")
    case True
    then show ?thesis using 20 assms unfolding  astack_dup.simps updateEnv.simps by (simp split:if_split_asm option.splits)
  next
    case False
    then show ?thesis using 20 assms unfolding  astack_dup.simps updateEnv.simps by (simp split:if_split_asm option.splits)
  qed
next
  case (21 x t p wi wj cd wk wl c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m)"
  obtain m'' where m'_def: "\<exists>x. (x, m'') = allocate m" unfolding allocate_def by simp
  have vkl:"wi = Calldata (MTArray x t) \<and> 0 < x\<and> denvalue env $$ i = None" using 21 by  (simp split:if_split_asm)
  then show ?thesis
  proof (cases "cpm2m p l x t cd m''")
    case None
    with 21 l_def m'_def show ?thesis unfolding allocate_def by  (simp split:if_split_asm)
  next
    case s2: (Some a)
    then have cc:"(c', m', k', env') = (c, a, astack_dup i (Memory (MTArray x t)) (KMemptr \<lfloor>toploc m\<rfloor>) (k, env))"
        using 21 assms l_def vkl m'_def unfolding allocate_def by simp
    then show ?thesis 
    proof(cases "i=ii")
      case True
      then show ?thesis using assms cc 21 unfolding allocate_def astack_dup.simps updateEnv.simps by simp

    next
      case False
      then show ?thesis using assms cc 21 unfolding allocate_def astack_dup.simps updateEnv.simps by (simp split:if_split_asm option.splits)
    qed  
  qed
next
  case (22 x t p x' t' wm wn wo s c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m)"
  obtain m'' where m'_def: "\<exists>x. (x, m'') = allocate m" unfolding allocate_def by simp
  have vkl:"cps2mTypeCompatible (STArray x' t') (MTArray x t)\<and> denvalue env $$ i = None" using 22 by (simp split:if_split_asm)
  show ?thesis
  proof (cases "cps2m p l x' t' s m''")
    case None
    with 22 l_def m'_def show ?thesis unfolding allocate_def by (simp split:if_split_asm)
  next
    case s2: (Some a)
    then have cc:"(c', m', k', env') = (c, a, astack_dup i (Memory (MTArray x t)) (KMemptr \<lfloor>toploc m\<rfloor>) (k, env))"
        using 22 assms l_def vkl m'_def unfolding allocate_def by simp
    then show ?thesis 
    proof(cases "i=ii")
      case True
      then show ?thesis using assms cc 22 unfolding allocate_def astack_dup.simps updateEnv.simps by simp

    next
      case False
      then show ?thesis using assms cc 22 unfolding allocate_def astack_dup.simps updateEnv.simps by (simp split:if_split_asm option.splits)
    qed  
  qed
next
  case (23 v wr ws wt wu wv ww)
  then show ?thesis by simp
next
  case (24 va v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (25 wq vc vb ws wt wu wv ww)
  then show ?thesis by simp
next
  case (26 v vc vb ws wt wu wv ww)
  then show ?thesis by simp
next
  case (27 v vc vb ws wt wu wv ww)
  then show ?thesis by simp
next
  case (28 wq vc v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (29 wq vc v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (30 wq vc v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (31 wq vc va vd ws wt wu wv ww)
  then show ?thesis by simp
next
  case (32 wq vc va ws wt wu wv ww)
  then show ?thesis by simp
next
  case (33 va v wt wu wv ww)
  then show ?thesis by simp
next
  case (34 wq vc vb wt wu wv ww)
  then show ?thesis by simp
next
  case (35 v vc vb wt wu wv ww)
  then show ?thesis by simp
next
  case (36 v vc vb wt wu wv ww)
  then show ?thesis by simp
next
  case (37 wq vc v wt wu wv ww)
  then show ?thesis by simp
next
  case (38 wq vc v wt wu wv ww)
  then show ?thesis by simp
next
  case (39 wq vc v wt wu wv ww)
  then show ?thesis by simp
next
  case (40 wq vc va vd wt wu wv ww)
  then show ?thesis by simp
next
  case (41 wq vc va wt wu wv ww)
  then show ?thesis by simp
next
  case (42 x t p wx wy wz xa xb c m k env)
  then show ?thesis
  proof(cases " i = ii")
    case True
    then show ?thesis using 42 assms unfolding  astack_dup.simps updateEnv.simps by (simp split:if_split_asm option.splits)
  next
    case False
    then show ?thesis using 42 assms unfolding  astack_dup.simps updateEnv.simps by (simp split:if_split_asm option.splits)
  qed
next
  case (43 t t' p xc xd xe xf xg c m k e)
  then show ?thesis  
  proof(cases " i = ii")
    case True
    then show ?thesis using 43 assms unfolding  astack_dup.simps updateEnv.simps by (simp split:if_split_asm option.splits)
  next
    case False
    then show ?thesis using 43 assms unfolding  astack_dup.simps updateEnv.simps by (simp split:if_split_asm option.splits)
  qed
next
  case (44 v va xk xl xm xn xo)
  then show ?thesis by simp
next
  case (45 v va ve vd xk xl xm xn xo)
  then show ?thesis by simp
next
  case (46 v va ve vd xk xl xm xn xo)
  then show ?thesis by simp
next
  case (47 v va ve vd xk xl xm xn xo)
  then show ?thesis by simp
next
  case (48 v xj xk xl xm xn xo)
  then show ?thesis by simp
next
  case (49 xi xk xl xm xn xo)
  then show ?thesis by simp
next
  case (50 xi vc vb xk xl xm xn xo)
  then show ?thesis by simp
next
  case (51 xi vc vb xk xl xm xn xo)
  then show ?thesis by simp
next
  case (52 xi vc vb xk xl xm xn xo)
  then show ?thesis by simp
qed

lemma decl_env_not_i:
  assumes "decl i tp a3 cp cd mem sto (c, m, k, env) = Some (c', m', k', env')"
    and " denvalue env' $$ ii = Some x"
    and "ii \<noteq> i"
  shows "denvalue env $$ ii = Some x"
  using assms
proof (cases rule:decl.elims)
  case (1 t uu uv uw ux c m k env)
  then show ?thesis using assms by (auto split:option.splits)
next
  case (2 t v t' uy uz va vb c m k e)
  show ?thesis
  proof (cases "convert t' t v")
    case None
    with 2 show ?thesis by simp
  next
    case s: (Some a)
    with 2 s show ?thesis using assms by (auto split:option.splits)
  qed
next
  case (3 vd ve vb vf vg vh vi vj)
  then show ?thesis by simp
next
  case (4 vd ve vb vf vg vh vi vj)
  then show ?thesis by simp
next
  case (5 vd ve vb vf vg vh vi vj)
  then show ?thesis by simp
next
  case (6 vd va ve vf vg vh vi vj)
  then show ?thesis by simp
next
  case (7 vd va ve vf vg vh vi vj)
  then show ?thesis by simp
next
  case (8 vd va ve vf vg vh vi vj)
  then show ?thesis by simp
next
  case (9 x t p vk cd vl vm c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc c)"
  obtain c''' where c_def: "\<exists>x. (x, c''') = allocate c" unfolding allocate_def by simp
  have vkl:" vk = Calldata (MTArray x t) \<and> 0 < x \<and> denvalue env $$ i = None" using 9 by (simp split:if_split_asm)
  show ?thesis
  proof (cases "cpm2m p l x t cd c'''")
    case None
    with 9 l_def c_def show ?thesis unfolding allocate_def by (simp split:if_split_asm)
  next
    case s2: (Some a)
    then have endc:"(c', m', k', env') = (a, m, astack_dup i (Calldata (MTArray x t)) (KCDptr l) (k, env))"
      using 9 l_def c_def vkl 
      by (metis (mono_tags, lifting) bind.bind_lunit case_prod_conv option.inject)
    show ?thesis 
    proof(cases "i = ii")
      case True
      with 9 endc show ?thesis using assms unfolding allocate_def astack_dup.simps by auto
    next
      case False
      then have "denvalue env $$ ii = denvalue env' $$ ii" 
        using endc assms unfolding allocate_def astack_dup.simps updateEnv.simps allocate_def by (simp split:if_split_asm option.splits)
      with 9 l_def c_def show ?thesis using assms unfolding allocate_def astack_dup.simps  by (simp split:if_split_asm option.splits)
    qed
       
  qed
next
  case (10 x t p vn vo mem vp c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc c)"
  obtain c''' where c_def: "\<exists>x. (x, c''') = allocate c" unfolding allocate_def by simp
  have vkl:"vn = Memory (MTArray x t) \<and> 0 < x\<and> denvalue env $$ i = None" using 10 by (simp split:if_split_asm)
  show ?thesis
  proof (cases "cpm2m p l x t mem c'''")
    case None
    with 10 l_def c_def show ?thesis unfolding allocate_def by (simp split:if_split_asm)
  next
    case s2: (Some a)
    then have endc:"(c', m', k', env') = (a, m, astack_dup i (Calldata (MTArray x t)) (KCDptr l) (k, env))"
      using 10 l_def c_def vkl 
      by (metis (mono_tags, lifting) bind.bind_lunit case_prod_conv option.inject)
    show ?thesis
    proof(cases "i = ii")
      case True
      with 10 endc show ?thesis using assms unfolding allocate_def astack_dup.simps by auto
    next
      case False
      then have "denvalue env $$ ii = denvalue env' $$ ii" 
        using endc assms unfolding allocate_def astack_dup.simps updateEnv.simps allocate_def by (simp split:if_split_asm option.splits)
      with 10 l_def c_def show ?thesis using assms unfolding allocate_def astack_dup.simps  by (simp split:if_split_asm option.splits)
    qed
  qed
next
  case (11 v vr vs vt vu vv vw)
  then show ?thesis by simp
next
  case (12 vq vs vt vu vv vw)
  then show ?thesis by simp
next
  case (13 vq vc vb vs vt vu vv vw)
  then show ?thesis by simp
next
  case (14 v vc vb vs vt vu vv vw)
  then show ?thesis by simp
next
  case (15 vq vc vb vt vu vv vw)
  then show ?thesis by simp
next
  case (16 vq vc vb vs vt vu vv vw)
  then show ?thesis by simp
next
  case (17 vq vr vt vu vv vw)
  then show ?thesis by simp
next
  case (18 x t vx vy vz wa c m k env)
  then show ?thesis 
  proof(cases " i = ii")
    case True
    then show ?thesis using 18 assms unfolding  astack_dup.simps updateEnv.simps by (simp split:if_split_asm option.splits)
  next
    case False
    then show ?thesis using 18 assms unfolding  astack_dup.simps updateEnv.simps by (simp split:if_split_asm option.splits)
  qed
next
  case (19 x t p wb wc mem wd c m k env)
  show ?thesis
  proof (cases cp)
    case True
    define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m)"
    obtain m'' where m'_def: "\<exists>x. (x, m'') = allocate m" unfolding allocate_def by simp
    have vkl:"wb = Memory (MTArray x t) \<and> 0 < x\<and> denvalue env $$ i = None" using 19 by (simp split:if_split_asm)
    then show ?thesis
    proof (cases "cpm2m p l x t mem m''")
      case None
      with 19 l_def m'_def show ?thesis unfolding allocate_def by (simp split:if_split_asm)
    next
      case s2: (Some a)
      then have cc:"(c', m', k', env') = (c, a, astack_dup i (Memory (MTArray x t)) (KMemptr \<lfloor>toploc m\<rfloor>) (k, env))"
        using 19 assms l_def vkl m'_def unfolding allocate_def by simp
      then show ?thesis 
      proof(cases "i=ii")
        case True
        then show ?thesis using assms cc 19 unfolding allocate_def astack_dup.simps updateEnv.simps by simp

      next
        case False
        then show ?thesis using assms cc 19 unfolding allocate_def astack_dup.simps updateEnv.simps by (simp split:if_split_asm option.splits)
      qed  
        
    qed
  next
    case False
    with 19 show ?thesis by simp
  qed
next
  case (20 x t p we wf wg wh c m k env)
  then show ?thesis
  proof(cases " i = ii")
    case True
    then show ?thesis using 20 assms unfolding  astack_dup.simps updateEnv.simps by (simp split:if_split_asm option.splits)
  next
    case False
    then show ?thesis using 20 assms unfolding  astack_dup.simps updateEnv.simps by (simp split:if_split_asm option.splits)
  qed
next
  case (21 x t p wi wj cd wk wl c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m)"
  obtain m'' where m'_def: "\<exists>x. (x, m'') = allocate m" unfolding allocate_def by simp
  have vkl:"wi = Calldata (MTArray x t) \<and> 0 < x\<and> denvalue env $$ i = None" using 21 by  (simp split:if_split_asm)
  then show ?thesis
  proof (cases "cpm2m p l x t cd m''")
    case None
    with 21 l_def m'_def show ?thesis unfolding allocate_def by  (simp split:if_split_asm)
  next
    case s2: (Some a)
    then have cc:"(c', m', k', env') = (c, a, astack_dup i (Memory (MTArray x t)) (KMemptr \<lfloor>toploc m\<rfloor>) (k, env))"
        using 21 assms l_def vkl m'_def unfolding allocate_def by simp
    then show ?thesis 
    proof(cases "i=ii")
      case True
      then show ?thesis using assms cc 21 unfolding allocate_def astack_dup.simps updateEnv.simps by simp

    next
      case False
      then show ?thesis using assms cc 21 unfolding allocate_def astack_dup.simps updateEnv.simps by (simp split:if_split_asm option.splits)
    qed  
  qed
next
  case (22 x t p x' t' wm wn wo s c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m)"
  obtain m'' where m'_def: "\<exists>x. (x, m'') = allocate m" unfolding allocate_def by simp
  have vkl:"cps2mTypeCompatible (STArray x' t') (MTArray x t)\<and> denvalue env $$ i = None" using 22 by (simp split:if_split_asm)
  show ?thesis
  proof (cases "cps2m p l x' t' s m''")
    case None
    with 22 l_def m'_def show ?thesis unfolding allocate_def by (simp split:if_split_asm)
  next
    case s2: (Some a)
    then have cc:"(c', m', k', env') = (c, a, astack_dup i (Memory (MTArray x t)) (KMemptr \<lfloor>toploc m\<rfloor>) (k, env))"
        using 22 assms l_def vkl m'_def unfolding allocate_def by simp
    then show ?thesis 
    proof(cases "i=ii")
      case True
      then show ?thesis using assms cc 22 unfolding allocate_def astack_dup.simps updateEnv.simps by simp

    next
      case False
      then show ?thesis using assms cc 22 unfolding allocate_def astack_dup.simps updateEnv.simps by (simp split:if_split_asm option.splits)
    qed  
  qed
next
  case (23 v wr ws wt wu wv ww)
  then show ?thesis by simp
next
  case (24 va v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (25 wq vc vb ws wt wu wv ww)
  then show ?thesis by simp
next
  case (26 v vc vb ws wt wu wv ww)
  then show ?thesis by simp
next
  case (27 v vc vb ws wt wu wv ww)
  then show ?thesis by simp
next
  case (28 wq vc v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (29 wq vc v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (30 wq vc v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (31 wq vc va vd ws wt wu wv ww)
  then show ?thesis by simp
next
  case (32 wq vc va ws wt wu wv ww)
  then show ?thesis by simp
next
  case (33 va v wt wu wv ww)
  then show ?thesis by simp
next
  case (34 wq vc vb wt wu wv ww)
  then show ?thesis by simp
next
  case (35 v vc vb wt wu wv ww)
  then show ?thesis by simp
next
  case (36 v vc vb wt wu wv ww)
  then show ?thesis by simp
next
  case (37 wq vc v wt wu wv ww)
  then show ?thesis by simp
next
  case (38 wq vc v wt wu wv ww)
  then show ?thesis by simp
next
  case (39 wq vc v wt wu wv ww)
  then show ?thesis by simp
next
  case (40 wq vc va vd wt wu wv ww)
  then show ?thesis by simp
next
  case (41 wq vc va wt wu wv ww)
  then show ?thesis by simp
next
  case (42 x t p wx wy wz xa xb c m k env)
  then show ?thesis
  proof(cases " i = ii")
    case True
    then show ?thesis using 42 assms unfolding  astack_dup.simps updateEnv.simps by (simp split:if_split_asm option.splits)
  next
    case False
    then show ?thesis using 42 assms unfolding  astack_dup.simps updateEnv.simps by (simp split:if_split_asm option.splits)
  qed
next
  case (43 t t' p xc xd xe xf xg c m k e)
  then show ?thesis  
  proof(cases " i = ii")
    case True
    then show ?thesis using 43 assms unfolding  astack_dup.simps updateEnv.simps by (simp split:if_split_asm option.splits)
  next
    case False
    then show ?thesis using 43 assms unfolding  astack_dup.simps updateEnv.simps by (simp split:if_split_asm option.splits)
  qed
next
  case (44 v va xk xl xm xn xo)
  then show ?thesis by simp
next
  case (45 v va ve vd xk xl xm xn xo)
  then show ?thesis by simp
next
  case (46 v va ve vd xk xl xm xn xo)
  then show ?thesis by simp
next
  case (47 v va ve vd xk xl xm xn xo)
  then show ?thesis by simp
next
  case (48 v xj xk xl xm xn xo)
  then show ?thesis by simp
next
  case (49 xi xk xl xm xn xo)
  then show ?thesis by simp
next
  case (50 xi vc vb xk xl xm xn xo)
  then show ?thesis by simp
next
  case (51 xi vc vb xk xl xm xn xo)
  then show ?thesis by simp
next
  case (52 xi vc vb xk xl xm xn xo)
  then show ?thesis by simp
qed

lemma decl_some_same:
  assumes "decl i tp a3 cp cd mem sto (c, m, k, env) = Some (c', m', k', env')"
    and " denvalue env $$ i = Some x"
  shows "env' = env \<and> c = c' \<and> m = m' \<and> k = k'"
  using assms
proof (cases rule:decl.elims)
  case (1 t uu uv uw ux c m k env)
  then show ?thesis using assms unfolding astack_dup.simps by simp
next
  case (2 t v t' uy uz va vb c m k e)
  show ?thesis
  proof (cases "convert t' t v")
    case None
    with 2 show ?thesis by simp
  next
    case s: (Some a)
    with 2 s show ?thesis using assms by (auto split:option.splits)
  qed
next
  case (3 vd ve vb vf vg vh vi vj)
  then show ?thesis by simp
next
  case (4 vd ve vb vf vg vh vi vj)
  then show ?thesis by simp
next
  case (5 vd ve vb vf vg vh vi vj)
  then show ?thesis by simp
next
  case (6 vd va ve vf vg vh vi vj)
  then show ?thesis by simp
next
  case (7 vd va ve vf vg vh vi vj)
  then show ?thesis by simp
next
  case (8 vd va ve vf vg vh vi vj)
  then show ?thesis by simp
next
  case (9 x t p vk cd vl vm c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc c)"
  obtain c''' where c_def: "\<exists>x. (x, c''') = allocate c" unfolding allocate_def by simp
  have vkl:" vk = Calldata (MTArray x t) \<and> 0 < x \<and> denvalue env $$ i = None" using 9 by (simp split:if_split_asm)
  then show ?thesis using assms 9 by simp
next
  case (10 x t p vn vo mem vp c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc c)"
  obtain c''' where c_def: "\<exists>x. (x, c''') = allocate c" unfolding allocate_def by simp
  have vkl:"vn = Memory (MTArray x t) \<and> 0 < x\<and> denvalue env $$ i = None" using 10 by (simp split:if_split_asm)
  then show ?thesis using assms 10 by simp
 
  
next
  case (11 v vr vs vt vu vv vw)
  then show ?thesis by simp
next
  case (12 vq vs vt vu vv vw)
  then show ?thesis by simp
next
  case (13 vq vc vb vs vt vu vv vw)
  then show ?thesis by simp
next
  case (14 v vc vb vs vt vu vv vw)
  then show ?thesis by simp
next
  case (15 vq vc vb vt vu vv vw)
  then show ?thesis by simp
next
  case (16 vq vc vb vs vt vu vv vw)
  then show ?thesis by simp
next
  case (17 vq vr vt vu vv vw)
  then show ?thesis by simp
next
  case (18 x t vx vy vz wa c m k env)
  then show ?thesis 
    using 18 assms unfolding  astack_dup.simps updateEnv.simps by (simp split:if_split_asm option.splits)
  
next
  case (19 x t p wb wc mem wd c m k env)
  show ?thesis
  proof (cases cp)
    case True
    define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m)"
    obtain m'' where m'_def: "\<exists>x. (x, m'') = allocate m" unfolding allocate_def by simp
    have vkl:"wb = Memory (MTArray x t) \<and> 0 < x\<and> denvalue env $$ i = None" using 19 by (simp split:if_split_asm)
    then show ?thesis using assms 19 by simp
  next
    case False
    with 19 show ?thesis by simp
  qed
next
  case (20 x t p we wf wg wh c m k env)
  then show ?thesis using 20 assms unfolding  astack_dup.simps updateEnv.simps by (simp split:if_split_asm option.splits)
next
  case (21 x t p wi wj cd wk wl c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m)"
  obtain m'' where m'_def: "\<exists>x. (x, m'') = allocate m" unfolding allocate_def by simp
  have vkl:"wi = Calldata (MTArray x t) \<and> 0 < x\<and> denvalue env $$ i = None" using 21 by  (simp split:if_split_asm)
  then show ?thesis
  proof (cases "cpm2m p l x t cd m''")
    case None
    with 21 l_def m'_def show ?thesis unfolding allocate_def by  (simp split:if_split_asm)
  next
    case s2: (Some a)
    then have cc:"(c', m', k', env') = (c, a, astack_dup i (Memory (MTArray x t)) (KMemptr \<lfloor>toploc m\<rfloor>) (k, env))"
        using 21 assms l_def vkl m'_def unfolding allocate_def by simp
    then show ?thesis 
    using assms cc 21 unfolding allocate_def astack_dup.simps updateEnv.simps by simp

   
  qed
next
  case (22 x t p x' t' wm wn wo s c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m)"
  obtain m'' where m'_def: "\<exists>x. (x, m'') = allocate m" unfolding allocate_def by simp
  have vkl:"cps2mTypeCompatible (STArray x' t') (MTArray x t)\<and> denvalue env $$ i = None" using 22 by (simp split:if_split_asm)
  show ?thesis
        using 22 assms l_def vkl m'_def unfolding allocate_def by simp
    
next
  case (23 v wr ws wt wu wv ww)
  then show ?thesis by simp
next
  case (24 va v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (25 wq vc vb ws wt wu wv ww)
  then show ?thesis by simp
next
  case (26 v vc vb ws wt wu wv ww)
  then show ?thesis by simp
next
  case (27 v vc vb ws wt wu wv ww)
  then show ?thesis by simp
next
  case (28 wq vc v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (29 wq vc v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (30 wq vc v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (31 wq vc va vd ws wt wu wv ww)
  then show ?thesis by simp
next
  case (32 wq vc va ws wt wu wv ww)
  then show ?thesis by simp
next
  case (33 va v wt wu wv ww)
  then show ?thesis by simp
next
  case (34 wq vc vb wt wu wv ww)
  then show ?thesis by simp
next
  case (35 v vc vb wt wu wv ww)
  then show ?thesis by simp
next
  case (36 v vc vb wt wu wv ww)
  then show ?thesis by simp
next
  case (37 wq vc v wt wu wv ww)
  then show ?thesis by simp
next
  case (38 wq vc v wt wu wv ww)
  then show ?thesis by simp
next
  case (39 wq vc v wt wu wv ww)
  then show ?thesis by simp
next
  case (40 wq vc va vd wt wu wv ww)
  then show ?thesis by simp
next
  case (41 wq vc va wt wu wv ww)
  then show ?thesis by simp
next
  case (42 x t p wx wy wz xa xb c m k env)
  then show ?thesis
  using 42 assms unfolding  astack_dup.simps updateEnv.simps by (simp split:if_split_asm option.splits)
  
next
  case (43 t t' p xc xd xe xf xg c m k e)
  then show ?thesis  
  using 43 assms unfolding  astack_dup.simps updateEnv.simps by (simp split:if_split_asm option.splits)
  
next
  case (44 v va xk xl xm xn xo)
  then show ?thesis by simp
next
  case (45 v va ve vd xk xl xm xn xo)
  then show ?thesis by simp
next
  case (46 v va ve vd xk xl xm xn xo)
  then show ?thesis by simp
next
  case (47 v va ve vd xk xl xm xn xo)
  then show ?thesis by simp
next
  case (48 v xj xk xl xm xn xo)
  then show ?thesis by simp
next
  case (49 xi xk xl xm xn xo)
  then show ?thesis by simp
next
  case (50 xi vc vb xk xl xm xn xo)
  then show ?thesis by simp
next
  case (51 xi vc vb xk xl xm xn xo)
  then show ?thesis by simp
next
  case (52 xi vc vb xk xl xm xn xo)
  then show ?thesis by simp
qed

lemma decl_storage_tp:
  assumes "decl i tp a3 cp cd mem sto (c, m, k, env) = Some (c', m', k', env')"
    and "denvalue env $$ i = None"
    and "denvalue env' $$ i = Some (Storage tt, Stackloc  (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc k)))"
  shows "\<exists>p. a3 = (Some (KStoptr p, Storage tt)) "
  using assms
proof (cases rule:decl.elims)
  case (1 t uu uv uw ux c m k env)
  then have "denvalue env' $$ i = Some (Value t, Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc k)))" 
    using assms by simp
  then show ?thesis using assms by simp
next
  case (2 t v t' uy uz va vb c m k e)
  show ?thesis
  proof (cases "convert t' t v")
    case None
    with 2 show ?thesis by simp
  next
    case s: (Some a)
    with 2 s show ?thesis using assms by (auto split:option.splits)
  qed
next
  case (3 vd ve vb vf vg vh vi vj)
  then show ?thesis by simp
next
  case (4 vd ve vb vf vg vh vi vj)
  then show ?thesis by simp
next
  case (5 vd ve vb vf vg vh vi vj)
  then show ?thesis by simp
next
  case (6 vd va ve vf vg vh vi vj)
  then show ?thesis by simp
next
  case (7 vd va ve vf vg vh vi vj)
  then show ?thesis by simp
next
  case (8 vd va ve vf vg vh vi vj)
  then show ?thesis by simp
next
  case (9 x t p vk cd vl vm c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc c)"
  obtain c''' where c_def: "\<exists>x. (x, c''') = allocate c" unfolding allocate_def by simp
  have vkl:" vk = Calldata (MTArray x t) \<and> 0 < x \<and> denvalue env $$ i = None" using 9 by (simp split:if_split_asm)
  then show ?thesis using assms 
    by (metis "9"(1) Type.simps(14) decl_env_storage)
  
       
  
next
  case (10 x t p vn vo mem vp c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc c)"
  obtain c''' where c_def: "\<exists>x. (x, c''') = allocate c" unfolding allocate_def by simp
  have vkl:"vn = Memory (MTArray x t) \<and> 0 < x\<and> denvalue env $$ i = None" using 10 by (simp split:if_split_asm)
  then show ?thesis 
    by (metis "10"(1,7) Type.simps(14) assms(1,3) decl_env_storage)
next
  case (11 v vr vs vt vu vv vw)
  then show ?thesis by simp
next
  case (12 vq vs vt vu vv vw)
  then show ?thesis by simp
next
  case (13 vq vc vb vs vt vu vv vw)
  then show ?thesis by simp
next
  case (14 v vc vb vs vt vu vv vw)
  then show ?thesis by simp
next
  case (15 vq vc vb vt vu vv vw)
  then show ?thesis by simp
next
  case (16 vq vc vb vs vt vu vv vw)
  then show ?thesis by simp
next
  case (17 vq vr vt vu vv vw)
  then show ?thesis by simp
next
  case (18 x t vx vy vz wa c m k env)
  then show ?thesis 
    using assms(2,3) by (auto split:option.splits if_splits)
next
  case (19 x t p wb wc mem wd c m k env)
  then show ?thesis 
    by (metis Option.option.simps(3) Type.simps(16) assms(1,3) decl_env_storage)
next
  case (20 x t p we wf wg wh c m k env)
  then show ?thesis 
    by (metis Type.simps(16) assms(1,3) decl_env_storage not_None_eq)
next
  case (21 x t p wi wj cd wk wl c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m)"
  obtain m'' where m'_def: "\<exists>x. (x, m'') = allocate m" unfolding allocate_def by simp
  have vkl:"wi = Calldata (MTArray x t) \<and> 0 < x\<and> denvalue env $$ i = None" using 21 by  (simp split:if_split_asm)
  then show ?thesis 
    by (metis "21"(1) Type.simps(16) assms(1,2,3) decl_env_storage)
next
  case (22 x t p x' t' wm wn wo s c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m)"
  obtain m'' where m'_def: "\<exists>x. (x, m'') = allocate m" unfolding allocate_def by simp
  have vkl:"cps2mTypeCompatible (STArray x' t') (MTArray x t)\<and> denvalue env $$ i = None" using 22 by (simp split:if_split_asm)
  show ?thesis 
    by (metis "22"(1) Type.distinct(11) assms(1,2,3) decl_env_storage)
next
  case (23 v wr ws wt wu wv ww)
  then show ?thesis by simp
next
  case (24 va v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (25 wq vc vb ws wt wu wv ww)
  then show ?thesis by simp
next
  case (26 v vc vb ws wt wu wv ww)
  then show ?thesis by simp
next
  case (27 v vc vb ws wt wu wv ww)
  then show ?thesis by simp
next
  case (28 wq vc v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (29 wq vc v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (30 wq vc v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (31 wq vc va vd ws wt wu wv ww)
  then show ?thesis by simp
next
  case (32 wq vc va ws wt wu wv ww)
  then show ?thesis by simp
next
  case (33 va v wt wu wv ww)
  then show ?thesis by simp
next
  case (34 wq vc vb wt wu wv ww)
  then show ?thesis by simp
next
  case (35 v vc vb wt wu wv ww)
  then show ?thesis by simp
next
  case (36 v vc vb wt wu wv ww)
  then show ?thesis by simp
next
  case (37 wq vc v wt wu wv ww)
  then show ?thesis by simp
next
  case (38 wq vc v wt wu wv ww)
  then show ?thesis by simp
next
  case (39 wq vc v wt wu wv ww)
  then show ?thesis by simp
next
  case (40 wq vc va vd wt wu wv ww)
  then show ?thesis by simp
next
  case (41 wq vc va wt wu wv ww)
  then show ?thesis by simp
next
  case (42 x' t' p' wx wy wz xa xb c m k'' env)
  then have wxDef:"wx = Storage (STArray x' t') \<and> denvalue env $$ i = None"
    by (auto split:if_splits)
  then have " (c', m', k', env') = (c, m, astack_dup i (Storage (STArray x' t')) (KStoptr p') (k, env))"
    using 42 by simp
  then have k'Def:"(k',env') = (push (KStoptr p') k, updateEnv i (Storage (STArray x' t')) (Stackloc \<lfloor>toploc k\<rfloor>) env)" 
    unfolding astack_dup.simps using wxDef by auto
  then have "denvalue env' $$ i = Some ((Storage (STArray x' t')), (Stackloc \<lfloor>toploc k\<rfloor>))" 
    unfolding updateEnv.simps by simp
  then have "tt = (STArray x' t')" using assms by simp
  
  moreover have "accessStore \<lfloor>toploc k\<rfloor> k' = Some (KStoptr p')" using k'Def unfolding push_def allocate_def updateStore_def accessStore_def by simp
  moreover have "a3 = Some (KStoptr p', Storage tt)" using 42 wxDef 
    using calculation(1) by simp
  moreover have "Storage tt = tp" using 42
    using calculation(1) by force
  ultimately show ?thesis using 42 wxDef by auto
next
  case (43 t t' p xc xd xe xf xg c m k e)
  then have wxDef:"xc = Storage (STMap t t') \<and> denvalue e $$ i = None"
    by (auto split:if_splits)
  then have " (c', m', k', env') = (c, m, astack_dup i (Storage (STMap t t') ) (KStoptr p) (k, e))"
    using 43 by simp
  then have k'Def:"(k',env') = (push (KStoptr p) k, updateEnv i (Storage ((STMap t t'))) (Stackloc \<lfloor>toploc k\<rfloor>) e)" 
    unfolding astack_dup.simps using wxDef by auto
  then have "denvalue env' $$ i = Some ((Storage ((STMap t t') )), (Stackloc \<lfloor>toploc k\<rfloor>))" 
    unfolding updateEnv.simps by simp
  show ?thesis using 43 wxDef assms by auto
next
  case (44 v va xk xl xm xn xo)
  then show ?thesis by simp
next
  case (45 v va ve vd xk xl xm xn xo)
  then show ?thesis by simp
next
  case (46 v va ve vd xk xl xm xn xo)
  then show ?thesis by simp
next
  case (47 v va ve vd xk xl xm xn xo)
  then show ?thesis by simp
next
  case (48 v xj xk xl xm xn xo)
  then show ?thesis by simp
next
  case (49 xi xk xl xm xn xo)
  then show ?thesis by simp
next
  case (50 xi vc vb xk xl xm xn xo)
  then show ?thesis by simp
next
  case (51 xi vc vb xk xl xm xn xo)
  then show ?thesis by simp
next
  case (52 xi vc vb xk xl xm xn xo)
  then show ?thesis by simp
qed


lemma decl_stack_top:
  assumes "decl i tp a3 cp cd mem sto (c, m, k, env) = Some (c', m', k', env')"
    and "denvalue env $$ i = None"
  shows "\<exists>t. denvalue env' $$ i = Some (t, Stackloc  (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc k)))" 
  using assms
proof (cases rule:decl.elims)
  case (1 t uu uv uw ux c m k env)
  then have "denvalue env' $$ i = Some (Value t, Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc k)))" 
    using assms by simp
  then show ?thesis using 1 by simp
next
  case (2 t v t' uy uz va vb c m k e)
  show ?thesis
  proof (cases "convert t' t v")
    case None
    with 2 show ?thesis by simp
  next
    case s: (Some a)
    with 2 s show ?thesis using assms by (auto split:option.splits)
  qed
next
  case (3 vd ve vb vf vg vh vi vj)
  then show ?thesis by simp
next
  case (4 vd ve vb vf vg vh vi vj)
  then show ?thesis by simp
next
  case (5 vd ve vb vf vg vh vi vj)
  then show ?thesis by simp
next
  case (6 vd va ve vf vg vh vi vj)
  then show ?thesis by simp
next
  case (7 vd va ve vf vg vh vi vj)
  then show ?thesis by simp
next
  case (8 vd va ve vf vg vh vi vj)
  then show ?thesis by simp
next
 case (9 x t p vk cd vl vm c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc c)"
  obtain c''' where c_def: "\<exists>x. (x, c''') = allocate c" unfolding allocate_def by simp
  have vkl:" vk = Calldata (MTArray x t) \<and> 0 < x \<and> denvalue env $$ i = None" using 9 by (simp split:if_split_asm)
  show ?thesis
  proof (cases "cpm2m p l x t cd c'''")
    case None
    with 9 l_def c_def show ?thesis unfolding allocate_def by (simp split:if_split_asm)
  next
    case s2: (Some a)
    then have endc:"(c', m', k', env') = (a, m, astack_dup i (Calldata (MTArray x t)) (KCDptr l) (k, env))"
      using 9 l_def c_def vkl 
      by (metis (mono_tags, lifting) bind.bind_lunit case_prod_conv option.inject)
    show ?thesis
    using endc 9 assms unfolding astack_dup.simps updateEnv.simps by simp
       
  qed
next
  case (10 x t p vn vo mem vp c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc c)"
  obtain c''' where c_def: "\<exists>x. (x, c''') = allocate c" unfolding allocate_def by simp
  have vkl:"vn = Memory (MTArray x t) \<and> 0 < x\<and> denvalue env $$ i = None" using 10 by (simp split:if_split_asm)
  show ?thesis
  proof (cases "cpm2m p l x t mem c'''")
    case None
    with 10 l_def c_def show ?thesis unfolding allocate_def by (simp split:if_split_asm)
  next
    case s2: (Some a)
    then have endc:"(c', m', k', env') = (a, m, astack_dup i (Calldata (MTArray x t)) (KCDptr l) (k, env))"
      using 10 l_def c_def vkl 
      by (metis (mono_tags, lifting) bind.bind_lunit case_prod_conv option.inject)
    show ?thesis using endc 10 assms unfolding astack_dup.simps updateEnv.simps by simp
  qed
next
  case (11 v vr vs vt vu vv vw)
  then show ?thesis by simp
next
  case (12 vq vs vt vu vv vw)
  then show ?thesis by simp
next
  case (13 vq vc vb vs vt vu vv vw)
  then show ?thesis by simp
next
  case (14 v vc vb vs vt vu vv vw)
  then show ?thesis by simp
next
  case (15 vq vc vb vt vu vv vw)
  then show ?thesis by simp
next
  case (16 vq vc vb vs vt vu vv vw)
  then show ?thesis by simp
next
  case (17 vq vr vt vu vv vw)
  then show ?thesis by simp
next
  case (18 x t vx vy vz wa c m k env)
  then show ?thesis  using 18 assms unfolding  astack_dup.simps updateEnv.simps by (simp split:if_split_asm option.splits)
  
next
  case (19 x t p wb wc mem wd c m k env)
  show ?thesis
  proof (cases cp)
    case True
    define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m)"
    obtain m'' where m'_def: "\<exists>x. (x, m'') = allocate m" unfolding allocate_def by simp
    have vkl:"wb = Memory (MTArray x t) \<and> 0 < x\<and> denvalue env $$ i = None" using 19 by (simp split:if_split_asm)
    then show ?thesis
    proof (cases "cpm2m p l x t mem m''")
      case None
      with 19 l_def m'_def show ?thesis unfolding allocate_def by (simp split:if_split_asm)
    next
      case s2: (Some a)
      then have cc:"(c', m', k', env') = (c, a, astack_dup i (Memory (MTArray x t)) (KMemptr \<lfloor>toploc m\<rfloor>) (k, env))"
        using 19 assms l_def vkl m'_def unfolding allocate_def by simp
      then show ?thesis using cc 19 assms unfolding astack_dup.simps updateEnv.simps by simp
        
    qed
  next
    case False
    with 19 show ?thesis by simp
  qed
next
  case (20 x t p we wf wg wh c m k env)
  then show ?thesis using 20 assms unfolding astack_dup.simps updateEnv.simps by (simp split:if_split_asm)
 
next
  case (21 x t p wi wj cd wk wl c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m)"
  obtain m'' where m'_def: "\<exists>x. (x, m'') = allocate m" unfolding allocate_def by simp
  have vkl:"wi = Calldata (MTArray x t) \<and> 0 < x\<and> denvalue env $$ i = None" using 21 by  (simp split:if_split_asm)
  then show ?thesis
  proof (cases "cpm2m p l x t cd m''")
    case None
    with 21 l_def m'_def show ?thesis unfolding allocate_def by  (simp split:if_split_asm)
  next
    case s2: (Some a)
    then have cc:"(c', m', k', env') = (c, a, astack_dup i (Memory (MTArray x t)) (KMemptr \<lfloor>toploc m\<rfloor>) (k, env))"
        using 21 assms l_def vkl m'_def unfolding allocate_def by simp
    then show ?thesis using cc 21 assms unfolding astack_dup.simps updateEnv.simps by simp
   
  qed
next
  case (22 x t p x' t' wm wn wo s c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m)"
  obtain m'' where m'_def: "\<exists>x. (x, m'') = allocate m" unfolding allocate_def by simp
  have vkl:"cps2mTypeCompatible (STArray x' t') (MTArray x t)\<and> denvalue env $$ i = None" using 22 by (simp split:if_split_asm)
  show ?thesis
  proof (cases "cps2m p l x' t' s m''")
    case None
    with 22 l_def m'_def show ?thesis unfolding allocate_def by (simp split:if_split_asm)
  next
    case s2: (Some a)
    then have cc:"(c', m', k', env') = (c, a, astack_dup i (Memory (MTArray x t)) (KMemptr \<lfloor>toploc m\<rfloor>) (k, env))"
        using 22 assms l_def vkl m'_def unfolding allocate_def by simp
    then show ?thesis using cc 22 assms unfolding astack_dup.simps updateEnv.simps by simp
  qed
next
  case (23 v wr ws wt wu wv ww)
  then show ?thesis by simp
next
  case (24 va v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (25 wq vc vb ws wt wu wv ww)
  then show ?thesis by simp
next
  case (26 v vc vb ws wt wu wv ww)
  then show ?thesis by simp
next
  case (27 v vc vb ws wt wu wv ww)
  then show ?thesis by simp
next
  case (28 wq vc v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (29 wq vc v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (30 wq vc v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (31 wq vc va vd ws wt wu wv ww)
  then show ?thesis by simp
next
  case (32 wq vc va ws wt wu wv ww)
  then show ?thesis by simp
next
  case (33 va v wt wu wv ww)
  then show ?thesis by simp
next
  case (34 wq vc vb wt wu wv ww)
  then show ?thesis by simp
next
  case (35 v vc vb wt wu wv ww)
  then show ?thesis by simp
next
  case (36 v vc vb wt wu wv ww)
  then show ?thesis by simp
next
  case (37 wq vc v wt wu wv ww)
  then show ?thesis by simp
next
  case (38 wq vc v wt wu wv ww)
  then show ?thesis by simp
next
  case (39 wq vc v wt wu wv ww)
  then show ?thesis by simp
next
  case (40 wq vc va vd wt wu wv ww)
  then show ?thesis by simp
next
  case (41 wq vc va wt wu wv ww)
  then show ?thesis by simp
next
  case (42 x t p wx wy wz xa xb c m k env)
  then show ?thesis using 42 assms unfolding astack_dup.simps updateEnv.simps by (simp split:if_split_asm option.splits)
  
next
  case (43 t t' p xc xd xe xf xg c m k e)
  then show ?thesis  using  assms unfolding astack_dup.simps updateEnv.simps by (simp split:if_split_asm option.splits)
 
next
  case (44 v va xk xl xm xn xo)
  then show ?thesis by simp
next
  case (45 v va ve vd xk xl xm xn xo)
  then show ?thesis by simp
next
  case (46 v va ve vd xk xl xm xn xo)
  then show ?thesis by simp
next
  case (47 v va ve vd xk xl xm xn xo)
  then show ?thesis by simp
next
  case (48 v xj xk xl xm xn xo)
  then show ?thesis by simp
next
  case (49 xi xk xl xm xn xo)
  then show ?thesis by simp
next
  case (50 xi vc vb xk xl xm xn xo)
  then show ?thesis by simp
next
  case (51 xi vc vb xk xl xm xn xo)
  then show ?thesis by simp
next
  case (52 xi vc vb xk xl xm xn xo)
  then show ?thesis by simp
qed

lemma decl_stack_topLoc:
  assumes "decl i tp (Some (KStoptr p2, Storage tt)) cp cd mem sto (c, m, k, env) = Some (c', m', k', env')"
    and "denvalue env $$ i = None"
    and "\<exists>p. accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc k)) k' = Some (KStoptr p)"
  shows "accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc k)) k' = Some (KStoptr p2)" 
  using assms
proof (cases rule:decl.elims)
  case (1 t uu uv uw ux c m k env)
  then have "denvalue env' $$ i = Some (Value t, Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc k)))" 
    using assms by simp
  then show ?thesis using 1 by simp
next
  case (2 t v t' uy uz va vb c m k e)
  show ?thesis
  proof (cases "convert t' t v")
    case None
    with 2 show ?thesis by simp
  next
    case s: (Some a)
    with 2 s show ?thesis using assms by (auto split:option.splits)
  qed
next
  case (3 vd ve vb vf vg vh vi vj)
  then show ?thesis by simp
next
  case (4 vd ve vb vf vg vh vi vj)
  then show ?thesis by simp
next
  case (5 vd ve vb vf vg vh vi vj)
  then show ?thesis by simp
next
  case (6 vd va ve vf vg vh vi vj)
  then show ?thesis by simp
next
  case (7 vd va ve vf vg vh vi vj)
  then show ?thesis by simp
next
  case (8 vd va ve vf vg vh vi vj)
  then show ?thesis by simp
next
 case (9 x t p vk cd vl vm c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc c)"
  obtain c''' where c_def: "\<exists>x. (x, c''') = allocate c" unfolding allocate_def by simp
  have vkl:" vk = Calldata (MTArray x t) \<and> 0 < x \<and> denvalue env $$ i = None" using 9 by (simp split:if_split_asm)
  show ?thesis
  proof (cases "cpm2m p l x t cd c'''")
    case None
    with 9 l_def c_def show ?thesis unfolding allocate_def by (simp split:if_split_asm)
  next
    case s2: (Some a)
    then have endc:"(c', m', k', env') = (a, m, astack_dup i (Calldata (MTArray x t)) (KCDptr l) (k, env))"
      using 9 l_def c_def vkl 
      by (metis (mono_tags, lifting) bind.bind_lunit case_prod_conv option.inject)
    show ?thesis
    using endc 9 assms unfolding astack_dup.simps updateEnv.simps by simp
       
  qed
next
  case (10 x t p vn vo mem vp c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc c)"
  obtain c''' where c_def: "\<exists>x. (x, c''') = allocate c" unfolding allocate_def by simp
  have vkl:"vn = Memory (MTArray x t) \<and> 0 < x\<and> denvalue env $$ i = None" using 10 by (simp split:if_split_asm)
  show ?thesis
  proof (cases "cpm2m p l x t mem c'''")
    case None
    with 10 l_def c_def show ?thesis unfolding allocate_def by (simp split:if_split_asm)
  next
    case s2: (Some a)
    then have endc:"(c', m', k', env') = (a, m, astack_dup i (Calldata (MTArray x t)) (KCDptr l) (k, env))"
      using 10 l_def c_def vkl 
      by (metis (mono_tags, lifting) bind.bind_lunit case_prod_conv option.inject)
    show ?thesis using endc 10 assms unfolding astack_dup.simps updateEnv.simps by simp
  qed
next
  case (11 v vr vs vt vu vv vw)
  then show ?thesis by simp
next
  case (12 vq vs vt vu vv vw)
  then show ?thesis by simp
next
  case (13 vq vc vb vs vt vu vv vw)
  then show ?thesis by simp
next
  case (14 v vc vb vs vt vu vv vw)
  then show ?thesis by simp
next
  case (15 vq vc vb vt vu vv vw)
  then show ?thesis by simp
next
  case (16 vq vc vb vs vt vu vv vw)
  then show ?thesis by simp
next
  case (17 vq vr vt vu vv vw)
  then show ?thesis by simp
next
  case (18 x t vx vy vz wa c m k env)
  then show ?thesis 
  using 18 assms unfolding  astack_dup.simps updateEnv.simps by (simp split:if_split_asm option.splits)
  
next
  case (19 x t p wb wc mem wd c m k env)
  show ?thesis
  proof (cases cp)
    case True
    define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m)"
    obtain m'' where m'_def: "\<exists>x. (x, m'') = allocate m" unfolding allocate_def by simp
    have vkl:"wb = Memory (MTArray x t) \<and> 0 < x\<and> denvalue env $$ i = None" using 19 by (simp split:if_split_asm)
    then show ?thesis
    proof (cases "cpm2m p l x t mem m''")
      case None
      with 19 l_def m'_def show ?thesis unfolding allocate_def by (simp split:if_split_asm)
    next
      case s2: (Some a)
      then have cc:"(c', m', k', env') = (c, a, astack_dup i (Memory (MTArray x t)) (KMemptr \<lfloor>toploc m\<rfloor>) (k, env))"
        using 19 assms l_def vkl m'_def unfolding allocate_def by simp
      then show ?thesis using cc 19 assms unfolding astack_dup.simps updateEnv.simps by simp
        
    qed
  next
    case False
    with 19 show ?thesis by simp
  qed
next
  case (20 x t p we wf wg wh c m k env)
  then show ?thesis using 20 assms unfolding astack_dup.simps updateEnv.simps by (simp split:if_split_asm)
 
next
  case (21 x t p wi wj cd wk wl c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m)"
  obtain m'' where m'_def: "\<exists>x. (x, m'') = allocate m" unfolding allocate_def by simp
  have vkl:"wi = Calldata (MTArray x t) \<and> 0 < x\<and> denvalue env $$ i = None" using 21 by  (simp split:if_split_asm)
  then show ?thesis
  proof (cases "cpm2m p l x t cd m''")
    case None
    with 21 l_def m'_def show ?thesis unfolding allocate_def by  (simp split:if_split_asm)
  next
    case s2: (Some a)
    then have cc:"(c', m', k', env') = (c, a, astack_dup i (Memory (MTArray x t)) (KMemptr \<lfloor>toploc m\<rfloor>) (k, env))"
        using 21 assms l_def vkl m'_def unfolding allocate_def by simp
    then show ?thesis using cc 21 assms unfolding astack_dup.simps updateEnv.simps by simp
   
  qed
next
  case (22 x t p x' t' wm wn wo s c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m)"
  obtain m'' where m'_def: "\<exists>x. (x, m'') = allocate m" unfolding allocate_def by simp
  have vkl:"cps2mTypeCompatible (STArray x' t') (MTArray x t)\<and> denvalue env $$ i = None" using 22 by (simp split:if_split_asm)
  show ?thesis
  proof (cases "cps2m p l x' t' s m''")
    case None
    with 22 l_def m'_def show ?thesis unfolding allocate_def by (simp split:if_split_asm)
  next
    case s2: (Some a)
    then have cc:"(c', m', k', env') = (c, a, astack_dup i (Memory (MTArray x t)) (KMemptr \<lfloor>toploc m\<rfloor>) (k, env))"
      using 22 assms l_def vkl m'_def unfolding allocate_def by simp
    then have "k' = push (KMemptr \<lfloor>toploc m\<rfloor>) k" unfolding astack_dup.simps using vkl by simp
    then have "accessStore \<lfloor>toploc k\<rfloor> k' = Some (KMemptr \<lfloor>toploc m\<rfloor>)" 
      unfolding accessStore_def updateStore_def push_def allocate_def by simp 
    then show ?thesis using assms(3) 22 by simp
  qed
next
  case (23 v wr ws wt wu wv ww)
  then show ?thesis by simp
next
  case (24 va v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (25 wq vc vb ws wt wu wv ww)
  then show ?thesis by simp
next
  case (26 v vc vb ws wt wu wv ww)
  then show ?thesis by simp
next
  case (27 v vc vb ws wt wu wv ww)
  then show ?thesis by simp
next
  case (28 wq vc v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (29 wq vc v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (30 wq vc v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (31 wq vc va vd ws wt wu wv ww)
  then show ?thesis by simp
next
  case (32 wq vc va ws wt wu wv ww)
  then show ?thesis by simp
next
  case (33 va v wt wu wv ww)
  then show ?thesis by simp
next
  case (34 wq vc vb wt wu wv ww)
  then show ?thesis by simp
next
  case (35 v vc vb wt wu wv ww)
  then show ?thesis by simp
next
  case (36 v vc vb wt wu wv ww)
  then show ?thesis by simp
next
  case (37 wq vc v wt wu wv ww)
  then show ?thesis by simp
next
  case (38 wq vc v wt wu wv ww)
  then show ?thesis by simp
next
  case (39 wq vc v wt wu wv ww)
  then show ?thesis by simp
next
  case (40 wq vc va vd wt wu wv ww)
  then show ?thesis by simp
next
  case (41 wq vc va wt wu wv ww)
  then show ?thesis by simp
next
  case (42 x t p wx wy wz xa xb c m k env)
  then show ?thesis using 42 assms 
    unfolding astack_dup.simps push_def allocate_def updateStore_def accessStore_def by (simp split:if_split_asm option.splits)
  
next
  case (43 t t' p xc xd xe xf xg c m k e)
  then show ?thesis  using  assms unfolding astack_dup.simps push_def allocate_def updateStore_def accessStore_def by (simp split:if_split_asm option.splits)
 
next
  case (44 v va xk xl xm xn xo)
  then show ?thesis by simp
next
  case (45 v va ve vd xk xl xm xn xo)
  then show ?thesis by simp
next
  case (46 v va ve vd xk xl xm xn xo)
  then show ?thesis by simp
next
  case (47 v va ve vd xk xl xm xn xo)
  then show ?thesis by simp
next
  case (48 v xj xk xl xm xn xo)
  then show ?thesis by simp
next
  case (49 xi xk xl xm xn xo)
  then show ?thesis by simp
next
  case (50 xi vc vb xk xl xm xn xo)
  then show ?thesis by simp
next
  case (51 xi vc vb xk xl xm xn xo)
  then show ?thesis by simp
next
  case (52 xi vc vb xk xl xm xn xo)
  then show ?thesis by simp
qed

lemma decl_env_false_same_cd:
  assumes "decl i tp a3 False cd mem sto (c, m, k, env) = Some (c', m', k', env')"
  shows "c = c'"
  using assms
proof (cases rule:decl.elims)
  case (1 t uu uv uw ux c m k env)
  then show ?thesis using assms by (auto split:option.splits)
next
  case (2 t v t' uy uz va vb c m k e)
  show ?thesis
  proof (cases "convert t' t v")
    case None
    with 2 show ?thesis by simp
  next
    case s: (Some a)
    with 2 s show ?thesis using assms by (auto split:option.splits)
  qed
next
  case (3 vd ve vb vf vg vh vi vj)
  then show ?thesis by simp
next
  case (4 vd ve vb vf vg vh vi vj)
  then show ?thesis by simp
next
  case (5 vd ve vb vf vg vh vi vj)
  then show ?thesis by simp
next
  case (6 vd va ve vf vg vh vi vj)
  then show ?thesis by simp
next
  case (7 vd va ve vf vg vh vi vj)
  then show ?thesis by simp
next
  case (8 vd va ve vf vg vh vi vj)
  then show ?thesis by simp
next
  case (9 x t p vk cd vl vm c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc c)"
  obtain c''' where c_def: "\<exists>x. (x, c''') = allocate c" unfolding allocate_def by simp
  have vkl:" vk = Calldata (MTArray x t) \<and> 0 < x\<and> denvalue env $$ i = None" using 9 by (simp split:if_split_asm)
  show ?thesis using 9 by simp
next
  case (10 x t p vn vo mem vp c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc c)"
  obtain c''' where c_def: "\<exists>x. (x, c''') = allocate c" unfolding allocate_def by simp
  have vkl:"vn = Memory (MTArray x t) \<and> 0 < x\<and> denvalue env $$ i = None" using 10 by (simp split:if_split_asm)
  show ?thesis using 10 by simp
next
  case (11 v vr vs vt vu vv vw)
  then show ?thesis by simp
next
  case (12 vq vs vt vu vv vw)
  then show ?thesis by simp
next
  case (13 vq vc vb vs vt vu vv vw)
  then show ?thesis by simp
next
  case (14 v vc vb vs vt vu vv vw)
  then show ?thesis by simp
next
  case (15 vq vc vb vt vu vv vw)
  then show ?thesis by simp
next
  case (16 vq vc vb vs vt vu vv vw)
  then show ?thesis by simp
next
  case (17 vq vr vt vu vv vw)
  then show ?thesis by simp
next
  case (18 x t vx vy vz wa c m k env)
  then show ?thesis using 18 assms unfolding  astack_dup.simps updateEnv.simps by (simp split:if_split_asm option.splits)
  
next
  case (19 x t p wb wc mem wd c m k env)
  
    with 19 show ?thesis by simp
  
next
  case (20 x t p we wf wg wh c m k env)
  then show ?thesis
  using 20 assms unfolding  astack_dup.simps updateEnv.simps by (simp split:if_split_asm option.splits)
  
next
  case (21 x t p wi wj cd wk wl c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m)"
  obtain m'' where m'_def: "\<exists>x. (x, m'') = allocate m" unfolding allocate_def by simp
  have vkl:"wi = Calldata (MTArray x t) \<and> 0 < x\<and> denvalue env $$ i = None" using 21 by  (simp split:if_split_asm)
  then show ?thesis 
  proof (cases "cpm2m p l x t cd m''")
    case None
    with 21 l_def m'_def show ?thesis unfolding allocate_def by  (simp split:if_split_asm)
  next
    case s2: (Some a)
    then have cc:"(c', m', k', env') = (c, a, astack_dup i (Memory (MTArray x t)) (KMemptr \<lfloor>toploc m\<rfloor>) (k, env))"
        using 21 assms l_def vkl m'_def unfolding allocate_def by simp
    then show ?thesis  using assms cc 21 unfolding allocate_def astack_dup.simps updateEnv.simps by simp

  qed
next
  case (22 x t p x' t' wm wn wo s c m k env)
  define l where "l = ShowL\<^sub>n\<^sub>a\<^sub>t (toploc m)"
  obtain m'' where m'_def: "\<exists>x. (x, m'') = allocate m" unfolding allocate_def by simp
  have vkl:"cps2mTypeCompatible (STArray x' t') (MTArray x t)\<and> denvalue env $$ i = None" using 22 by (simp split:if_split_asm)
  show ?thesis
  proof (cases "cps2m p l x' t' s m''")
    case None
    with 22 l_def m'_def show ?thesis unfolding allocate_def by (simp split:if_split_asm)
  next
    case s2: (Some a)
    then have cc:"(c', m', k', env') = (c, a, astack_dup i (Memory (MTArray x t)) (KMemptr \<lfloor>toploc m\<rfloor>) (k, env))"
        using 22 assms l_def vkl m'_def unfolding allocate_def by simp
    then show ?thesis using assms cc 22 unfolding allocate_def astack_dup.simps updateEnv.simps by simp
  qed
next
  case (23 v wr ws wt wu wv ww)
  then show ?thesis by simp
next
  case (24 va v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (25 wq vc vb ws wt wu wv ww)
  then show ?thesis by simp
next
  case (26 v vc vb ws wt wu wv ww)
  then show ?thesis by simp
next
  case (27 v vc vb ws wt wu wv ww)
  then show ?thesis by simp
next
  case (28 wq vc v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (29 wq vc v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (30 wq vc v ws wt wu wv ww)
  then show ?thesis by simp
next
  case (31 wq vc va vd ws wt wu wv ww)
  then show ?thesis by simp
next
  case (32 wq vc va ws wt wu wv ww)
  then show ?thesis by simp
next
  case (33 va v wt wu wv ww)
  then show ?thesis by simp
next
  case (34 wq vc vb wt wu wv ww)
  then show ?thesis by simp
next
  case (35 v vc vb wt wu wv ww)
  then show ?thesis by simp
next
  case (36 v vc vb wt wu wv ww)
  then show ?thesis by simp
next
  case (37 wq vc v wt wu wv ww)
  then show ?thesis by simp
next
  case (38 wq vc v wt wu wv ww)
  then show ?thesis by simp
next
  case (39 wq vc v wt wu wv ww)
  then show ?thesis by simp
next
  case (40 wq vc va vd wt wu wv ww)
  then show ?thesis by simp
next
  case (41 wq vc va wt wu wv ww)
  then show ?thesis by simp
next
  case (42 x t p wx wy wz xa xb c m k env)
  then show ?thesis using 42 assms unfolding  astack_dup.simps updateEnv.simps by (simp split:if_split_asm option.splits)
  
next
  case (43 t t' p xc xd xe xf xg c m k e)
  then show ?thesis using 43 assms unfolding  astack_dup.simps updateEnv.simps by (simp split:if_split_asm option.splits)
 
next
  case (44 v va xk xl xm xn xo)
  then show ?thesis by simp
next
  case (45 v va ve vd xk xl xm xn xo)
  then show ?thesis by simp
next
  case (46 v va ve vd xk xl xm xn xo)
  then show ?thesis by simp
next
  case (47 v va ve vd xk xl xm xn xo)
  then show ?thesis by simp
next
  case (48 v xj xk xl xm xn xo)
  then show ?thesis by simp
next
  case (49 xi xk xl xm xn xo)
  then show ?thesis by simp
next
  case (50 xi vc vb xk xl xm xn xo)
  then show ?thesis by simp
next
  case (51 xi vc vb xk xl xm xn xo)
  then show ?thesis by simp
next
  case (52 xi vc vb xk xl xm xn xo)
  then show ?thesis by simp
qed

declare decl.simps[simp del, solidity_symbex add]
end
