section\<open>Defining the properties of type consistency for the memory datatypes Isabelle Hol\<close>
theory TypeSafe_Memory
  imports TypeSafe_Base_Types 
begin

definition AllocatedMem_between :: "MemoryT \<Rightarrow> MemoryT \<Rightarrow> Location set"
  where
    "AllocatedMem_between st st' = ({ShowL\<^sub>n\<^sub>a\<^sub>t l | l. toploc st \<le> l \<and> l < toploc st'}) 
                                  \<union> fset(fmdom (mapping (st')) - fmdom (mapping (st)))"

primrec CompMemJustType::"MTypes \<Rightarrow> MTypes \<Rightarrow> bool"
  where 
    "CompMemJustType (MTValue typ) mem  = (mem = MTValue typ)"
  | "CompMemJustType (MTArray len arr) mem  = (mem = (MTArray len arr) \<or> CompMemJustType arr mem)"

primrec CompMemType :: "MemoryT \<Rightarrow> nat \<Rightarrow> MTypes  \<Rightarrow> MTypes \<Rightarrow> Location \<Rightarrow> Location \<Rightarrow> bool"
  where 
    "CompMemType mem len (MTValue typ) childtp  parentloc childloc = (childtp = (MTValue typ) \<and> (\<exists>i<len. (hash parentloc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) = childloc))"
  | "CompMemType mem len (MTArray len' arr) childtp parentloc childloc = (\<exists>i<len. \<exists>l. accessStore (hash parentloc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem =  Some (MPointer l) \<and>
                                                                          ((l = childloc \<and> (MTArray len' arr) = childtp) \<or> CompMemType mem len' arr childtp l childloc)
                                                                        )"

fun GetAllMemoryLocations :: "MTypes \<Rightarrow> Location \<Rightarrow> MemoryT \<Rightarrow>  Location set"
  where
    "GetAllMemoryLocations (MTValue _) base_loc _ = {base_loc}"
  | "GetAllMemoryLocations (MTArray len struct) base_loc mem =
     (\<Union>i\<in>{0..<len}.
       (case accessStore (hash base_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem of
          Some (MPointer ptr) \<Rightarrow> {(hash base_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i))} \<union> GetAllMemoryLocations struct ptr mem
        | Some (MValue _) \<Rightarrow> {(hash base_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i))} \<union> GetAllMemoryLocations struct (hash base_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem
        | None \<Rightarrow> {}))"

(*
    Calculates the set of all memory locations that are reachable
     from the given environment and state.
    *)
primrec MCon :: "MTypes \<Rightarrow> MemoryT \<Rightarrow>  Location  \<Rightarrow> bool"
  where
    "MCon (MTValue typ) msto loc =(case (accessStore loc msto) of 
                                  (Some (MValue t)) \<Rightarrow> (typeCon typ t) 
                                    | (Some(MPointer t)) \<Rightarrow> False
                                    | None \<Rightarrow> False)"

|"MCon (MTArray len arr) msto loc = (len>0 \<and> (\<forall>i < len. 
                                                (case (accessStore (hash loc  (ShowL\<^sub>n\<^sub>a\<^sub>t i)) msto) of
                                                 (Some (MPointer loc2)) \<Rightarrow> 
                                                        (case arr of (MTArray len' arr') \<Rightarrow>  (MCon arr msto (loc2))
                                                            | MTValue val \<Rightarrow> False)
                                                  | Some(MValue val) \<Rightarrow> 
                                                    (case arr of (MTValue typ) \<Rightarrow>  (MCon arr msto (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
                                                      | (MTArray l a) \<Rightarrow> False)
                                                  | None \<Rightarrow> False)) 
                                    \<and> (\<exists>p. accessStore loc msto = Some (MPointer p) \<or> accessStore loc msto = None))"

primrec MConAccessSame:: "Location \<Rightarrow> Location \<Rightarrow> MTypes \<Rightarrow> MemoryT \<Rightarrow> MemoryT \<Rightarrow>  bool"
  where 
    "MConAccessSame l1 l2 (MTValue t) m1 m2 = (\<exists>val. accessStore l1 m1 = Some (MValue val) \<and> (\<exists>val'. accessStore l2 m2 = Some (MValue val')))"
  | "MConAccessSame l1 l2 (MTArray len t) m1 m2 = (\<forall>i1<len. \<forall>i2<len. (\<forall>l. accessStore (hash l1 (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) m1 = Some (MPointer l) \<longrightarrow> 
                                                                (\<exists>l'. accessStore (hash l2 (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) m2 = Some (MPointer l') 
                                                                \<and> MConAccessSame l l' t m1 m2)))"
fun ReachableMem :: "Environment \<Rightarrow> Stack \<Rightarrow> MemoryT \<Rightarrow> Location set"
  where
    "ReachableMem env st mem = (\<Union> (t, l) \<in> fset(fmran (denvalue env)).
         (case l of
           Stackloc loc \<Rightarrow>
             (case accessStore loc  st of
               Some (KMemptr ptr) \<Rightarrow>
                 (case t of
                   Memory struct \<Rightarrow> GetAllMemoryLocations struct ptr mem
                    | _ \<Rightarrow> {})
               | _ \<Rightarrow> {})
            | Storeloc loc \<Rightarrow> {}))"


primrec TypedMemSubPref:: "Location \<Rightarrow> Location \<Rightarrow> MTypes \<Rightarrow> bool"
  where 
    "TypedMemSubPref child parent (MTValue t) = (child = parent)"
  | "TypedMemSubPref child parent (MTArray len t) = (\<exists>i<len. TypedMemSubPref child (hash parent (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t \<or> child = (hash parent (ShowL\<^sub>n\<^sub>a\<^sub>t i)))"

primrec TypedMemSubPrefPtrs:: "MemoryT \<Rightarrow> nat \<Rightarrow> MTypes\<Rightarrow> Location \<Rightarrow> Location \<Rightarrow> bool"
  where 
    "TypedMemSubPrefPtrs mem len (MTValue t) parent child  = (\<exists>i<len. (hash parent (ShowL\<^sub>n\<^sub>a\<^sub>t i)) = child)"
  | "TypedMemSubPrefPtrs mem len (MTArray len' t) parent child  = (\<exists>i<len. \<exists>l. accessStore (hash parent (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l) 
                                                                  \<and> (l = child \<or> TypedMemSubPrefPtrs mem len' t l child ))"

definition WrittenMem_between :: "MemoryT \<Rightarrow> MemoryT \<Rightarrow> Location set"
  where
    "WrittenMem_between st st' = {l. accessStore l st \<noteq> accessStore l (st')}"

definition compMemPtrs :: "Stack \<Rightarrow> MemoryT \<Rightarrow> (String.literal, Type \<times> Denvalue) fmap \<Rightarrow> bool" where
  "compMemPtrs st mem denval = (\<forall>tp1 tp2 l1 l2 stl1 stl2 dloc1. 
          (Memory tp1, Stackloc l1) |\<in>| fmran denval \<and> (Memory tp2, Stackloc l2) |\<in>| fmran denval
          \<and> accessStore l1 st = Some(KMemptr stl1) \<and> accessStore l2 st = Some(KMemptr stl2)
      \<longrightarrow> (if stl1 = stl2 then tp1 = tp2 else
            (case tp1 of 
              MTValue val \<Rightarrow> 
                (case tp2 of MTValue val2 \<Rightarrow> True
                  | MTArray len2 arr2 \<Rightarrow> (if TypedMemSubPrefPtrs mem len2 arr2 stl2 stl1 then CompMemType mem len2 arr2 (MTValue val) stl2 stl1 
                                          else True))
             | MTArray len arr \<Rightarrow> 
                (case tp2 of MTValue val2 \<Rightarrow> (if TypedMemSubPrefPtrs mem len arr stl1 stl2 then CompMemType mem len arr (MTValue val2) stl1 stl2 
                                            else True)
                  | MTArray len2 arr2 \<Rightarrow> (if TypedMemSubPrefPtrs mem len2 arr2 stl2 stl1 then CompMemType mem len2 arr2 (MTArray len arr) stl2 stl1 
                                          else if TypedMemSubPrefPtrs mem len arr stl1 stl2 then CompMemType mem len arr (MTArray len2 arr2) stl1 stl2 
                                          else if (TypedMemSubPrefPtrs mem len arr stl1 dloc1 \<and> TypedMemSubPrefPtrs mem len2 arr2 stl2 dloc1)
                                                  then (\<exists>dt. CompMemType mem len2 arr2 dt stl2 dloc1 
                                                                         \<and> CompMemType mem len arr dt stl1 dloc1 
                                                                         )
                                          else True))

)))"

definition compMemPtrs3 :: "Stack \<Rightarrow> MemoryT \<Rightarrow> (String.literal, Type \<times> Denvalue) fmap \<Rightarrow> bool" where
  "compMemPtrs3 st mem denval = (\<forall>tp1 tp2 l1 l2 stl1 stl2 dloc1.
    (Memory tp1, Stackloc l1) |\<in>| fmran denval \<and> (Memory tp2, Stackloc l2) |\<in>| fmran denval
    \<and> accessStore l1 st = Some(KMemptr stl1) \<and> accessStore l2 st = Some(KMemptr stl2)
    \<longrightarrow> (if stl1 = stl2 then tp1 = tp2 else
      (case (tp1, tp2) of
          (MTValue val, MTValue val2) \<Rightarrow> True
        | (MTValue val, MTArray len2 arr2) \<Rightarrow> \<not> (TypedMemSubPrefPtrs mem len2 arr2 stl2 stl1) \<or> CompMemType mem len2 arr2 (MTValue val) stl2 stl1
        | (MTArray len arr, MTValue val2) \<Rightarrow> \<not> (TypedMemSubPrefPtrs mem len arr stl1 stl2) \<or> CompMemType mem len arr (MTValue val2) stl1 stl2
        | (MTArray len arr, MTArray len2 arr2) \<Rightarrow>
            if (TypedMemSubPrefPtrs mem len arr stl1 dloc1 \<and> TypedMemSubPrefPtrs mem len2 arr2 stl2 dloc1)
                then (\<exists>dt. CompMemType mem len2 arr2 dt stl2 dloc1 \<and> CompMemType mem len arr dt stl1 dloc1 )
            else True)
      )
    )"


fun extractType :: "MTypes \<Rightarrow> MTypes option" where
  "extractType (MTArray len arr) = Some arr"
| "extractType (MTValue v) = None"

fun mtype_size :: "MTypes \<Rightarrow> nat" where
  "mtype_size (MTValue _) = 1"
| "mtype_size (MTArray _ S) = 1 + mtype_size S"

lemma AllocatedMem_between_same_empty:
  shows "AllocatedMem_between st st = {}" unfolding AllocatedMem_between_def 
proof -
  have "\<not>(\<exists>l. toploc st \<le> l \<and> l < toploc st)" by auto
  then have "{(ShowL\<^sub>n\<^sub>a\<^sub>t l) |l. toploc st \<le> l \<and> l < toploc st} = {}" by blast

  then show "{(ShowL\<^sub>n\<^sub>a\<^sub>t l) |l. toploc st \<le> l \<and> l < toploc st} \<union> fset(fmdom (mapping st) |-| fmdom (mapping st)) =  {} "
    by blast
qed

lemma AllocatedMem_between_trans:
  assumes toploc_mono: "toploc m1 \<le> toploc m2" 
    and "toploc m2 \<le> toploc m3"
    and fmdom_mono: "fmdom (mapping m1) |\<subseteq>| fmdom (mapping m2)" and "fmdom (mapping m2) |\<subseteq>| fmdom (mapping m3)"
  shows "AllocatedMem_between m1 m2 \<union> AllocatedMem_between m2 m3 = AllocatedMem_between m1 m3"
proof -
  have toploc_eq: "({ShowL\<^sub>n\<^sub>a\<^sub>t l | l. toploc m1 \<le> l \<and> l < toploc 
      m2} \<union> {ShowL\<^sub>n\<^sub>a\<^sub>t l | l. toploc m2 \<le> l \<and> l < toploc m3}) =
                        {ShowL\<^sub>n\<^sub>a\<^sub>t l | l. toploc m1 \<le> l \<and> l < toploc 
      m3}"
    using assms(1,2) by fastforce

  have mapping_eq: "(fset (fmdom (mapping m2) - fmdom (mapping m1)) \<union> fset (fmdom (mapping m3) - fmdom (mapping m2))) 
                          = fset (fmdom (mapping m3) - fmdom (mapping m1))"
    using assms(3,4) by blast
  then show ?thesis using toploc_eq 
    using AllocatedMem_between_def by auto  
qed


lemma  CompMemJustType_exists_Val:
  shows "\<exists> x. CompMemJustType z (MTValue x)" 
proof(induction z)
  case (MTArray x1 z)
  then show ?case by simp
next
  case (MTValue x)
  then show ?case by simp
qed

lemma CompMemJustType_single_MTVal:
  assumes "CompMemJustType z (MTValue x)"
  shows "\<forall>b. CompMemJustType z (MTValue b) \<longrightarrow> b = x"
proof(intros)
  fix b 
  assume "CompMemJustType z (MTValue b)"
  then show "b = x" using assms 
  proof(induction z)
    case (MTArray x1 z)
    then show ?case by simp
  next
    case (MTValue x)
    then show ?case by simp
  qed
qed




lemma CompMemJustTypes_trns:
  assumes "CompMemJustType tp1 tp2"
    and "CompMemJustType tp1 tp3"
  shows "CompMemJustType tp2 tp3 \<or> CompMemJustType tp3 tp2" using assms
proof(induction tp1 arbitrary:tp2 tp3)
  case (MTArray x1 tp1)
  then show ?case by auto
next
  case (MTValue x)
  then show ?case by simp
qed



lemma CompMemType_imps_CompMemJustType:
  assumes "CompMemType mem len t1 t2 l1 l2"
  shows "CompMemJustType (MTArray len t1) t2" using assms 
proof(induction t1 arbitrary:l1 len)
  case (MTArray x1 t2')
  then show ?case 
  proof(cases "t2 = MTArray x1 t2'")
    case True
    then show ?thesis by simp
  next
    case False
    then have a10:"(\<exists>i<len. \<exists>l.  accessStore (hash l1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l) \<and> (l = l2 \<and> MTArray x1 t2' = t2 \<or> CompMemType mem x1 t2' t2 l l2))" 
      using MTArray(2) CompMemType.simps(2)[of mem len x1 t2' t2 l1 l2] by simp

    have "CompMemJustType t2' t2" 
      using False MTArray.IH a10 by auto
    then show ?thesis using False by simp
  qed
next
  case (MTValue x)
  then show ?case using CompMemJustType.simps(1) CompMemType.simps(1) by simp
qed

lemma CompMemType_imps_TypedMemSubPrefPtrs:
  assumes "CompMemType mem len tp tc lp lc"
  shows "TypedMemSubPrefPtrs mem len tp lp lc" using assms
proof(induction tp arbitrary:lp len)
  case (MTArray x1 tp)
  then have a10:"(\<exists>i<len. \<exists>l.  accessStore (hash lp (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l) \<and> ((l = lc ) \<and> MTArray x1 tp = tc \<or> CompMemType mem x1 tp tc l lc))" 
    using CompMemType.simps(2)[of mem len x1 tp tc lp lc] MTArray(2) by auto
  then obtain i where idef:"i<len" and 
    idef2:"(\<exists>l.  accessStore (hash lp (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l) \<and> ((l = lc ) \<and> MTArray x1 tp = tc \<or> CompMemType mem x1 tp tc l lc))" by auto
  then show ?case 
    using MTArray.IH by auto 
next
  case (MTValue x)
  then show ?case by simp
qed

lemma CompMemTypes_asc:
  assumes "CompMemJustType tp1 tp2"
    and "CompMemJustType tp2 tp3"
  shows "CompMemJustType tp1 tp3" using assms
proof(induction tp1)
  case (MTArray x1 tp1)
  then show ?case by auto
next
  case (MTValue x)
  then show ?case by simp
qed

lemma CopiedValues_In_AllocatedMem:
  assumes "x'' \<in> GetAllMemoryLocations mtype tloc (memory st')"
    and "\<forall>locs v. LSubPrefL2 locs tloc \<and> accessStore locs (memory st') = Some v \<longrightarrow> locs \<in> AllocatedMem_between (memory st) (memory st')"
    and "\<forall>l l'. LSubPrefL2 l tloc \<and> accessStore l (memory st') = Some (MPointer l') \<longrightarrow> l' = l"
    and "tloc \<in> AllocatedMem_between (memory st) (memory st')"
  shows "x'' \<in> AllocatedMem_between (memory st) (memory st')"
  using assms
proof(induction mtype arbitrary:tloc)
  case (MTArray x1 mtype)
  obtain i where idef:"i <x1 \<and> x''\<in> (case accessStore (hash tloc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (memory st') of None \<Rightarrow> {}
         | Some (MValue xa) \<Rightarrow> {hash tloc (ShowL\<^sub>n\<^sub>a\<^sub>t i)} \<union> GetAllMemoryLocations mtype (hash tloc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (memory st')
         | Some (MPointer ptr) \<Rightarrow> {hash tloc (ShowL\<^sub>n\<^sub>a\<^sub>t i)} \<union> GetAllMemoryLocations mtype ptr (memory st'))"
    using MTArray.prems(1) unfolding GetAllMemoryLocations.simps by auto
  then have subloc:"LSubPrefL2 (hash tloc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) tloc" unfolding LSubPrefL2_def by auto
  consider (ptr) ptr where "accessStore (hash tloc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (memory st') = Some (MPointer ptr)
                            \<and> i<x1 \<and> x'' \<in>{hash tloc (ShowL\<^sub>n\<^sub>a\<^sub>t i)} \<union> GetAllMemoryLocations mtype ptr (memory st')"
    | (val) val where "accessStore (hash tloc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (memory st') = Some (MValue val)
                            \<and> i<x1 \<and> x'' \<in>{hash tloc (ShowL\<^sub>n\<^sub>a\<^sub>t i)} \<union> GetAllMemoryLocations mtype (hash tloc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (memory st')" 
    using idef by (auto split:Memoryvalue.splits option.splits)
  then show ?case 
  proof(cases)
    case ptr
    then have isSame:"ptr = hash tloc (ShowL\<^sub>n\<^sub>a\<^sub>t i)" using MTArray.prems(3) subloc by blast
    then have inThere:"hash tloc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<in> AllocatedMem_between (memory st) (memory st')" using subloc MTArray.prems(2) ptr by blast
    then show ?thesis 
    proof(cases "hash tloc (ShowL\<^sub>n\<^sub>a\<^sub>t i) = x''")
      case True
      then show ?thesis using inThere by simp
    next
      case False
      then have "x'' \<in> GetAllMemoryLocations mtype ptr (memory st')" using ptr by blast
      moreover have "\<forall>locs v. LSubPrefL2 locs ptr \<and> accessStore locs (memory st') = Some v \<longrightarrow> locs \<in> AllocatedMem_between (memory st) (memory st')"
        using MTArray.prems(2) subloc LSubPrefL2_def isSame 
        by (meson Not_Sub_More_Specific)
      moreover have "\<forall>l l'. LSubPrefL2 l ptr \<and> accessStore l (memory st') = Some (MPointer l') \<longrightarrow> l' = l " using isSame MTArray.prems(3) 
        using Not_Sub_More_Specific by blast
      ultimately have "x'' \<in> AllocatedMem_between (memory st) (memory st')" using MTArray.IH[of ptr] 
        using inThere isSame by fastforce
      then show ?thesis by simp
    qed
  next
    case val
    then have inThere:"hash tloc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<in> AllocatedMem_between (memory st) (memory st')" using subloc MTArray.prems(2)  by blast
    then show ?thesis 
    proof(cases "hash tloc (ShowL\<^sub>n\<^sub>a\<^sub>t i) = x''")
      case True
      then show ?thesis using inThere by simp
    next
      case False
      then have "x'' \<in> GetAllMemoryLocations mtype (hash tloc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (memory st')" using val by blast
      moreover have "\<forall>locs v. LSubPrefL2 locs (hash tloc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) \<and> accessStore locs (memory st') = Some v \<longrightarrow> locs \<in> AllocatedMem_between (memory st) (memory st')"
        using MTArray.prems(2) subloc LSubPrefL2_def  
        by (meson Not_Sub_More_Specific)
      moreover have "\<forall>l l'. LSubPrefL2 l (hash tloc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) \<and> accessStore l (memory st') = Some (MPointer l') \<longrightarrow> l' = l " using  MTArray.prems(3) 
        using Not_Sub_More_Specific by blast
      ultimately have "x'' \<in> AllocatedMem_between (memory st) (memory st')" using MTArray.IH[of "(hash tloc (ShowL\<^sub>n\<^sub>a\<^sub>t i))"] 
        using inThere by fastforce
      then show ?thesis by simp
    qed
  qed
next
  case (MTValue x)
  then have "x'' = tloc" by auto
  then show ?case using MTValue by blast
qed


lemma MConArrayPointers:
  assumes "MCon (MTArray len (MTArray len' t)) v' loc"
    and "len >0"
    and "i < len" 
  obtains val where  "accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = Some (MPointer val)" 
proof -
  have a10:"\<forall>i<len.
             case accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'  of None \<Rightarrow> False
             | Some (MValue val) \<Rightarrow>
                 (case MTArray len' t of MTValue typ \<Rightarrow> MCon (MTArray len' t) v' (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i))
                  | _ \<Rightarrow> False)
             | Some (MPointer loc2) \<Rightarrow>
                 (case MTArray len' t of MTArray len'a arr' \<Rightarrow> MCon (MTArray len' t) v' loc2
                 | MTValue Types \<Rightarrow> False)" 
    using MCon.simps(2)[of len "MTArray len' t"  v' loc] assms(1) by simp
  show ?thesis
  proof(cases "accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'")
    case None
    then show ?thesis using a10 assms by auto
  next
    case (Some a)
    then show ?thesis 
    proof(cases a)
      case (MValue x1)
      then show ?thesis using a10 assms Some by auto
    next
      case (MPointer val)
      then show ?thesis using Some that by auto
    qed
  qed
qed




lemma MConIndexMin1:
  assumes "MCon (MTArray len t) v' loc"
    and "len -1 > 0"
  shows "MCon (MTArray (len-1) t) v' loc" using assms MCon.simps by simp

lemma MConTypeSplitingArray:
  assumes "\<forall>(i::nat)<(x1::nat).
             (case accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem of 
                Some (MPointer loc2) => 
                    (case tp1 of MTArray len' arr' => MCon tp1 mem loc2 
                               | MTValue tps => False)
              | Some (MValue val) => 
                    (case tp1 of (MTArray n mt) => False 
                                | MTValue tps => MCon tp1 mem (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
              | None => False)"
    and "\<exists>a b. tp1 = MTArray a b"  
    and "(i::nat)<x1"
  shows "\<exists>p. accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer p)" 
proof(cases "accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem")
  case None
  then show ?thesis using assms(1) assms(3) by auto
next
  case (Some a)
  then show ?thesis 
  proof(cases a)
    case (MValue x1)
    then show ?thesis using assms Some by auto
  next
    case (MPointer x2)
    then show ?thesis using assms Some by auto
  qed
qed

lemma MConSubTypes:
  assumes "MCon (MTArray len t') mem loc"
  shows "\<forall>t. CompMemJustType t' t \<longrightarrow> (\<not>MCon t mem loc)" using assms 
proof(induction t' arbitrary: len loc)
  case (MTArray x1 t')
  show ?case 
  proof intros
    fix t 
    assume *:"CompMemJustType (MTArray x1 t') t"
    then have a5:"t = MTArray x1 t' \<or> CompMemJustType t' t" by (cases t) auto

    have a10:" \<forall>i<len.
             case accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem of None \<Rightarrow> False
             | Some (MValue val) \<Rightarrow> (case MTArray x1 t' of MTArray n MTypes \<Rightarrow> False 
                                        | MTValue typ \<Rightarrow> MCon (MTArray x1 t') mem (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
             | Some (MPointer loc2) \<Rightarrow> (case MTArray x1 t' of MTArray len' arr' \<Rightarrow> MCon (MTArray x1 t') mem loc2 
                                        | MTValue Types \<Rightarrow> False)"
      using MTArray(2) MCon.simps(2)[of len "MTArray x1 t'" mem loc] by simp
    then obtain p' i where p'def:" i<len \<and>  accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer p')" 
      by (metis MConArrayPointers MTArray.prems(1) MCon.simps(2))
    then have a20:"MCon (MTArray x1 t') mem p'" using a10 by fastforce
    then have a30:"\<forall>t. CompMemJustType t' t \<longrightarrow> \<not> MCon t mem p'" using MTArray.IH by auto

    then show "\<not> MCon t mem loc" 
    proof(cases "t = MTArray x1 t'")
      case True
      show ?thesis 
      proof
        assume ***:"MCon t mem loc"
        then have a90:"\<forall>i<x1.
             (case accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem of None \<Rightarrow> False 
                  | Some (MValue val) \<Rightarrow> (case t' of MTArray n MTypes \<Rightarrow> False | MTValue typ \<Rightarrow> MCon t' mem (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
              | Some (MPointer loc2) \<Rightarrow> (case t' of MTArray len' arr' \<Rightarrow> MCon t' mem loc2 | MTValue Types \<Rightarrow> False))" 
          using MCon.simps(2)[of x1 t' mem loc ] using True by auto
        then obtain i' where i'Def:"i'<x1 \<and> i' <len" 
          using "*"  MTArray.prems \<open>MCon t mem loc\<close> 
          using True by fastforce 
        then obtain p'' where p''def: "accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i')) mem = Some (MPointer p'')" using a10  p'def MConTypeSplitingArray[of len "MTArray x1 t'" mem loc i'] by auto
        then have "MCon t' mem p''" using a90 i'Def 
          by (metis (no_types, lifting) MTypes.exhaust MTypes.simps(5) MTypes.simps(6) Memoryvalue.simps(6) Option.option.simps(5))
        moreover have "MCon (MTArray x1 t') mem p''" using p''def i'Def a10 by auto
        ultimately show False using a20 
          using "*"  MTArray.prems \<open>MCon t mem loc\<close> 
          by (metis MTArray.IH CompMemJustType.simps(1) CompMemJustType.simps(2) extractType.elims) 
      qed
    next
      case False
      then have "CompMemJustType t' t" using a5 by auto
      then have "\<not> MCon t mem p'" using a30 by auto
      show ?thesis
      proof
        assume ***:"MCon t mem loc"
        then show False
        proof(cases t)
          case mta:(MTArray x11 x12)
          then have c10:"\<forall>i<x11.
             (case accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem of None \<Rightarrow> False 
              | Some (MValue val) \<Rightarrow> (case x12 of MTArray n MTypes \<Rightarrow> False | MTValue typ \<Rightarrow> MCon x12 mem (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
              | Some (MPointer loc2) \<Rightarrow> (case x12 of MTArray len' arr' \<Rightarrow> MCon x12 mem loc2 | MTValue Types \<Rightarrow> False))" 
            using *** MCon.simps(2)[of x11 x12 mem loc] by simp
          then obtain i''' where i'''def:"i'''<x11 \<and> i'''<len" 
            by (metis "***" mta MTArray.prems neq0_conv MCon.simps(2))
          then obtain p'' where p''def: "accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i''')) mem = Some (MPointer p'')" 
            using a10  p'def MConTypeSplitingArray[of len "MTArray x1 t'" mem loc i'''] by auto
          then have "MCon (MTArray x1 t') mem p''" using a10 i'''def by fastforce
          have "MCon x12 mem p''" using i'''def p''def c10 mta 
            by (metis (no_types, lifting) MTypes.exhaust MTypes.simps(5) MTypes.simps(6) Memoryvalue.simps(6) Option.option.simps(5))
          then show ?thesis using MCon.simps(2)[of x11 x12 mem loc] 
            by (metis CompMemTypes_asc MTArray.IH \<open>CompMemJustType t' t\<close> \<open>MCon (MTArray x1 t') mem p''\<close> mta CompMemJustType.simps(1) CompMemJustType.simps(2) extractType.cases)
        next
          case (MTValue x2)
          then show ?thesis using p'def *** MCon.simps(1)[of x2 mem loc] 
            using MTArray.prems by force
        qed

      qed
    qed
  qed
next
  case (MTValue x) 
  show ?case 
  proof intros
    fix t 
    assume *:"CompMemJustType (MTValue x) t "
    then have **:"t = MTValue x" by simp
    moreover have "\<forall>i<len.
             case accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem of None \<Rightarrow> False 
             | Some (MValue val) \<Rightarrow> (case MTValue x of MTArray n MTypes \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTValue x) mem (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
             | Some (MPointer loc2) \<Rightarrow> (case MTValue x of MTArray len' arr' \<Rightarrow> MCon (MTValue x) mem loc2 | MTValue Types \<Rightarrow> False)" 
      using MTValue MCon.simps(2)[of len "MTValue x" mem loc] by auto
    then show "\<not> MCon t mem loc" using MTValue ** 
      by (metis Memoryvalue.simps(6) Option.option.simps(4) Option.option.simps(5) MCon.simps(1) MCon.simps(2))
  qed
qed

lemma MConPtrsMustBeSubLocs:
  assumes "MCon (MTArray len t') mem loc"
  shows "\<forall>p i. i<len \<and> accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer p) \<longrightarrow> p \<noteq> loc" 
proof intros
  fix i p 
  assume *:"i < len \<and> accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer p)"
  then have a10:"(case t' of MTArray len' arr' \<Rightarrow> MCon t' mem p | MTValue Types \<Rightarrow> False)" 
    using assms MCon.simps(2)[of len t' mem loc] by auto
  then have "MCon t' mem p" using * by (cases t'; simp)
  then show "p\<noteq>loc" using assms MConSubTypes[of len t' mem loc] 
    by (metis CompMemJustType.simps(1) CompMemJustType.simps(2) extractType.cases)
qed

lemma MConPtrsMustBeSubLocs2:
  assumes "MCon (MTArray len arr) mem loc"
  shows "\<forall>p t. MCon t mem p \<and> CompMemType mem len arr t loc p \<longrightarrow> p \<noteq> loc" using assms 
proof (induction arr arbitrary:len loc)
  case (MTArray x1 arr)
  show ?case 
  proof(intros)
    fix p t 
    assume *:"MCon t mem p \<and> CompMemType mem len (MTArray x1 arr) t loc p"
    then have a1:"CompMemJustType (MTArray len (MTArray x1 arr)) t" 
      using CompMemType_imps_CompMemJustType by blast 
    show "p \<noteq> loc" 
    proof
      assume **:"p = loc" 
      have "(\<exists>i<len. \<exists>l. accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l) 
            \<and> (l = p \<and> MTArray x1 arr = t \<or> CompMemType mem x1 arr t l p))" 
        using * CompMemType.simps(2)[of mem len x1 arr t loc p] by auto
      then obtain i l where idef:"i<len \<and>  accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l) 
                                  \<and> (l = p \<and> MTArray x1 arr = t \<or> CompMemType mem x1 arr t l p)" by blast
      then have "(case accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem of None \<Rightarrow> False 
              | Some (MValue val) \<Rightarrow> (case MTArray x1 arr of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTArray x1 arr) mem (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
              | Some (MPointer loc2) \<Rightarrow> (case MTArray x1 arr of MTArray len' arr' \<Rightarrow> MCon (MTArray x1 arr) mem loc2 | MTValue Types \<Rightarrow> False)) 
            \<and> ((\<exists>p. accessStore loc mem = Some (MPointer p)) \<or> accessStore loc mem = None)" 
        using MTArray(2) MCon.simps(2)[of len "MTArray x1 arr" mem loc] by metis
      then have "MCon (MTArray x1 arr) mem l" using idef by force
      show False 
      proof(cases "l = p \<and>  MTArray x1 arr = t")
        case True
        then show ?thesis 
          using "**" idef  
          using MConPtrsMustBeSubLocs MTArray.prems by blast
      next
        case False
        then have "CompMemType mem x1 arr t l p" using idef by auto
        then have "p \<noteq> l"   
          using "**"  MConPtrsMustBeSubLocs MTArray.prems MConSubTypes[of len "(MTArray x1 arr)" mem loc] a1 
          using idef by blast
        then show ?thesis 
          using "*" "**" CompMemType_imps_CompMemJustType MConSubTypes MTArray.prems \<open>CompMemType mem x1 arr t l p\<close> by blast
      qed
    qed
  qed
next
  case (MTValue x)
  then show ?case by fastforce
qed


lemma BothMConImpsNotCompMemType:
  assumes "MCon (MTArray len arr) mem p''"
    and "MCon t' mem p''"
  shows "\<not>CompMemType mem len arr t' p'' p''" using assms
proof(induction arr arbitrary:len p'')
  case (MTArray x1 arr)
  then show ?case 
    by (meson MConPtrsMustBeSubLocs2)
next
  case (MTValue x)
  then show ?case by fastforce
qed

lemma MConTypeSplitingValue:
  assumes "\<forall>(i::nat)<(x1::nat).
             (case accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem of 
                Some (MPointer loc2) => 
                    (case tp1 of MTArray len' arr' => MCon tp1 mem loc2 
                               | MTValue tps => False)
              | Some (MValue val) => 
                    (case tp1 of (MTArray n mt) => False 
                                | MTValue tps => MCon tp1 mem (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
              | None => False)"
    and "\<exists>a. tp1 = MTValue a"  
    and "i<x1"
  shows "\<exists>val. accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MValue val)" 
proof(cases "accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem")
  case None
  then show ?thesis using assms(1) assms(3) by auto
next
  case (Some a)
  then show ?thesis 
  proof(cases a)
    case (MValue x1)
    then show ?thesis using assms Some by auto
  next
    case (MPointer x2)
    then show ?thesis using assms Some by auto
  qed
qed

lemma MCon_imps_Some: 
  assumes "MCon t' mem p'"
  shows "\<exists>x i. accessStore p' mem = Some x \<or> accessStore (hash p' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some x"
proof(cases t')
  case (MTArray x11 x12)
  then have a10:"\<forall>i<x11.
             (case accessStore (hash p' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem of None \<Rightarrow> False
              | Some (MValue val) \<Rightarrow> (case x12 of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon x12 mem (hash p' (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
              | Some (MPointer loc2) \<Rightarrow> (case x12 of MTArray len' arr' \<Rightarrow> MCon x12 mem loc2 | MTValue Types \<Rightarrow> False))" 
    using assms MCon.simps(2)[of x11 x12 "mem" p'] by simp
  then obtain i where a20:"i<x11 " 
    using MTArray assms by fastforce
  then show ?thesis 
  proof(cases " accessStore (hash p' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem")
    case None
    then show ?thesis using a10 a20 by auto
  next
    case (Some a)
    then show ?thesis 
      by auto
  qed
next
  case (MTValue x2)
  then have a10:"(case accessStore p' mem of None \<Rightarrow> False | Some (MValue t) \<Rightarrow> typeCon x2 t | Some (MPointer t) \<Rightarrow> False)" 
    using assms(1) MCon.simps(1)[of x2 "mem" p'] by auto
  then show ?thesis 
  proof(cases "accessStore p' mem")
    case None
    then show ?thesis using a10 by simp
  next
    case (Some a)
    then show ?thesis by auto
  qed
qed

lemma MCon_subTypes_imps_noPrnt:
  assumes "MCon (MTArray x t) mem l"
    and "MCon (MTArray x' (MTArray x t)) mem l'"
  shows "\<not>CompMemType mem x t (MTArray x' (MTArray x t)) l l'" using assms 
  using CompMemType_imps_CompMemJustType MConSubTypes by blast

abbreviation mymemory2::MemoryT
  where "mymemory2 \<equiv>
    \<lparr>mapping = fmap_of_list
      [(STR ''1.1.0'', MValue STR ''False''),
       (STR ''0.1.0'', MValue STR ''True''),
       (STR ''1.0'', MPointer STR ''1.0''),
       (STR ''1.0.0'', MValue STR ''False''),
       (STR ''0.0.0'', MValue STR ''True''),
       (STR ''0.0'', MPointer STR ''0.0'')],
     toploc = 1\<rparr>"

lemma MCon_sub_MTVal_imps_val:
  assumes "MCon (MTArray len (MTValue t)) mm loc"
  shows "\<forall>i<len. \<exists>val. accessStore  (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mm = Some (MValue val)"
proof intros
  fix i 
  assume "i<len"
  then have a10:"case accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mm of None \<Rightarrow> False 
             | Some (MValue val) \<Rightarrow> (case MTValue t of MTArray n MTypes \<Rightarrow> False 
                                        | MTValue typ \<Rightarrow> MCon (MTValue t) mm (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
             | Some (MPointer loc2) \<Rightarrow> (case MTValue t of MTArray len' arr' \<Rightarrow> MCon (MTValue t) mm loc2 
                                          | MTValue Types \<Rightarrow> False)" 
    using assms(1) MCon.simps(2)[of len "MTValue t" mm loc] by simp
  show "\<exists>val. accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mm = Some (MValue val) "
  proof(cases "accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mm")
    case None
    then show ?thesis using a10 by simp
  next
    case (Some a)
    then show ?thesis 
    proof(cases a)
      case (MValue x1)
      then show ?thesis using a10 Some by auto
    next
      case (MPointer x2)
      then show ?thesis using a10 Some by auto
    qed
  qed
qed

lemma CompTypeRemainsMCon:
  assumes "CompMemType mem len arr t2 p' stl1"
    and "MCon (MTArray len arr) mem p'"
  shows "MCon t2 mem stl1" using assms
proof(induction arr arbitrary: len p')
  case (MTArray x1 arr)
  then have a10:"\<forall>i<len.
             (case accessStore (hash p' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem of 
               Some (MPointer loc2) \<Rightarrow>  MCon (MTArray x1 arr) mem loc2) \<and>
             ((\<exists>p. accessStore p' mem = Some (MPointer p)) \<or> accessStore p' mem = None)"
    using MCon.simps(2)[of len "MTArray x1 arr" mem p'] 
    by (metis MConArrayPointers MTypes.simps(5) Memoryvalue.simps(6) Option.option.simps(5))
  have "(\<exists>i<len. \<exists>l. accessStore (hash p' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l) 
        \<and> (l = stl1 \<and> MTArray x1 arr = t2 \<or> CompMemType mem x1 arr t2 l stl1))" 
    using MTArray CompMemType.simps(2)[of mem len x1 arr t2 p' stl1] by auto
  then obtain i l where idef:"i<len \<and> accessStore (hash p' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l) 
        \<and> (l = stl1 \<and> MTArray x1 arr = t2 \<or> CompMemType mem x1 arr t2 l stl1)" by blast
  then show ?case 
  proof(cases "l = stl1 \<and> MTArray x1 arr = t2")
    case True
    then show ?thesis using a10 idef by auto
  next
    case False
    then show ?thesis using MTArray.IH[of x1 l] a10 idef by fastforce
  qed
next
  case (MTValue x)
  then have a10:"\<forall>i<len.
             (case accessStore (hash p' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem of None \<Rightarrow> False 
              | Some (MValue val) \<Rightarrow> (case MTValue x of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTValue x) mem (hash p' (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
              | Some (MPointer loc2) \<Rightarrow> (case MTValue x of MTArray len' arr' \<Rightarrow> MCon (MTValue x) mem loc2 | MTValue Types \<Rightarrow> False)) \<and>
             ((\<exists>p. accessStore p' mem = Some (MPointer p)) \<or> accessStore p' mem = None)"
    using MCon.simps(2)[of len "MTValue x" mem p'] by simp
  have a20:"(t2 = MTValue x \<and> (\<exists>i<len. hash p' (ShowL\<^sub>n\<^sub>a\<^sub>t i) = stl1))" using MTValue CompMemType.simps(1)[of mem len x t2 p' stl1] by auto
  then obtain i where idef:"i<len \<and> hash p' (ShowL\<^sub>n\<^sub>a\<^sub>t i) = stl1" by auto
  then have "MCon (MTValue x) mem (hash p' (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using a10 
    by (metis MCon_sub_MTVal_imps_val MTValue.prems(2) MTypes.simps(6) Memoryvalue.simps(5) Option.option.simps(5))
  then show ?case using idef a20 by auto
qed




lemma GetAllMemoryLocations_Arry_Contains_Indexs:
  assumes "MCon (MTArray len2 arr2) mem stl2"
  shows "\<forall>i<len2. hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<in> GetAllMemoryLocations (MTArray len2 arr2) stl2 mem" using assms
proof(cases arr2)
  case (MTArray x1 arr2')
  show ?thesis 
  proof intros
    fix i 
    assume *:"i<len2"
    then have "\<exists>c. accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer c)" 
      using assms MTArray by (metis MConArrayPointers not_gr0 not_less0)
    then show "hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<in> GetAllMemoryLocations (MTArray len2 arr2) stl2 mem" 
      unfolding GetAllMemoryLocations.simps using * by fastforce
  qed
next
  case (MTValue x)
  have exp:"GetAllMemoryLocations (MTArray len2 (MTValue x)) stl2 mem = (\<Union>i\<in>{0..<len2}.
        case accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem of None \<Rightarrow> {} | Some (MValue xa) \<Rightarrow> {hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)} \<union> {hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)} | Some (MPointer ptr) \<Rightarrow> {hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)} \<union> {ptr})" 
    unfolding GetAllMemoryLocations.simps by blast
  show ?thesis 
  proof intros
    fix i assume *:"i<len2"
    then have "i \<in> {0..<len2}" by simp
    then have exp':"(case accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem of None \<Rightarrow> {} | Some (MValue xa) \<Rightarrow> {hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)} \<union> {hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)} | Some (MPointer ptr) \<Rightarrow> {hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)} \<union> {ptr})
\<subseteq> GetAllMemoryLocations (MTArray len2 (MTValue x)) stl2 mem" using exp by blast
    have "\<exists>c. accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MValue c)" using MTValue assms * 
      using MCon_sub_MTVal_imps_val by blast
    then have "(case accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem of None \<Rightarrow> {} | Some (MValue xa) \<Rightarrow> {hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)} \<union> {hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)} | Some (MPointer ptr) \<Rightarrow> {hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)} \<union> {ptr})
                    = {hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)}" by auto
    then have "{hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)} \<subseteq> GetAllMemoryLocations (MTArray len2 (MTValue x)) stl2 mem" using exp' by simp
    then show "hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<in> GetAllMemoryLocations (MTArray len2 arr2) stl2 mem" using MTValue by blast
  qed
qed

lemma MCon_imps_sub_Mcon: 
  assumes "MCon (MTArray arLen t) srcMem srcl"
  shows "\<forall>x::nat<arLen. (\<forall>l. accessStore (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) srcMem = Some (MPointer l) \<longrightarrow> MCon t srcMem l) 
      \<and> (\<forall>val. accessStore (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) srcMem = Some (MValue val) \<longrightarrow> MCon t srcMem (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)))"
  using assms
proof(induction t arbitrary: arLen srcl)
  case (MTArray x1 t)
  show ?case 
  proof(intros)
    fix x l 
    assume *:"x<arLen"
      and "accessStore (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) srcMem = Some (MPointer l)"
    then show "MCon (MTArray x1 t) srcMem l" using MTArray 
      by (meson CompTypeRemainsMCon CompMemType.simps(2))
  next
    fix x val
    assume *:"x<arLen"
      and "accessStore (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) srcMem = Some (MValue val)"
    then show "MCon (MTArray x1 t) srcMem (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" using MTArray by auto
  qed
next
  case (MTValue x)
  show ?case 
  proof(intros)
    fix xa l 
    assume *:"xa<arLen"
      and **:"accessStore (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t xa)) srcMem = Some (MPointer l)" 
    show "MCon (MTValue x) srcMem l" using * ** 
      using MTValue by force
  next
    fix xa val 
    assume *:"xa<arLen"
      and **:"accessStore (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t xa)) srcMem = Some (MValue val)" 
    show "MCon (MTValue x) srcMem (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t xa))" using * ** MTValue by auto
  qed
qed

lemma MconSameTypeSameAccess:
  assumes "MCon (MTArray x t) m1 l1"
    and "MCon (MTArray x t) m2 l2"
  shows "\<forall>i<x. (\<forall>l. accessStore (hash l1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m1 = Some (MPointer l) \<longrightarrow> (\<exists>l'. accessStore (hash l2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m2 = Some (MPointer l'))) 
        \<and> (\<forall>val . accessStore (hash l1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m1 = Some (MValue val) \<longrightarrow> (\<exists>val'. accessStore (hash l2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m2 = Some (MValue val')))" 
  using assms
proof(induction t arbitrary:x l1 l2)
  case (MTArray x1 t)
  show ?case 
  proof(intros)
    fix i l 
    assume *:"i<x" 
      and **:"accessStore (hash l1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m1 = Some (MPointer l)"
    show "\<exists>l'. accessStore (hash l2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m2 = Some (MPointer l')" using MTArray 
      by (metis "*" MConArrayPointers gr_zeroI less_nat_zero_code)
  next
    fix i val
    assume *:"i<x" 
      and **:" accessStore (hash l1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m1 = Some (MValue val)"
    show "\<exists>val'. accessStore (hash l2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m2 = Some (MValue val')" 
      using "*" "**" MTArray.prems(1) by fastforce
  qed
next
  case (MTValue x')
  show ?case
  proof(intros)
    fix i l 
    assume *:"i<x" 
      and **:"accessStore (hash l1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m1 = Some (MPointer l)"
    show "\<exists>l'. accessStore (hash l2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m2 = Some (MPointer l')" using * ** MTValue by auto
  next 
    fix i val 
    assume *:"i<x" 
      and **:"accessStore (hash l1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m1 = Some (MValue val)"
    have "(case accessStore (hash l2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m2 of None \<Rightarrow> False 
              | Some (MValue val) \<Rightarrow> (case MTValue x' of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTValue x') m2 (hash l2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
              | Some (MPointer loc2) \<Rightarrow> (case MTValue x' of MTArray len' arr' \<Rightarrow> MCon (MTValue x') m2 loc2 | MTValue Types \<Rightarrow> False))"
      using MTValue(2) MCon.simps(2)[of x "MTValue x'" m2 l2] * by simp
    then have "\<exists>l. accessStore (hash l2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m2 = Some (MValue l)" 
      by (auto split:option.splits MTypes.splits Memoryvalue.splits)
    then show "\<exists>val'. accessStore (hash l2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m2 = Some (MValue val')"  by auto
  qed
qed

lemma MconSameTypeSameAccessWithTyping:
  assumes "MCon (MTArray x t) m1 l1"
    and "MCon (MTArray x t) m2 l2"
  shows "\<forall>i1<x. \<forall>i2<x. (\<forall>l. accessStore (hash l1 (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) m1 = Some (MPointer l) \<longrightarrow> (\<exists>l'. accessStore (hash l2 (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) m2 = Some (MPointer l') \<and> MCon t m1 l \<and> MCon t m2 l')) 
        \<and> (\<forall>val . accessStore (hash l1 (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) m1 = Some (MValue val) \<longrightarrow> (\<exists>val'. accessStore (hash l2 (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) m2 = Some (MValue val')\<and> MCon t m1 (hash l1 (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) \<and> MCon t m2 (hash l2 (ShowL\<^sub>n\<^sub>a\<^sub>t i2))))" 
  using assms
proof(induction t arbitrary:x l1 l2)
  case (MTArray x1 t)
  show ?case 
  proof(intros)
    fix i1 i2 l 
    assume *:"i1<x" and ***:"i2<x"
      and **:"accessStore (hash l1 (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) m1 = Some (MPointer l)"
    then have "MCon (MTArray x1 t) m1 l" using MTArray 
      by (meson CompTypeRemainsMCon CompMemType.simps(2))
    moreover have "\<exists>l'. accessStore (hash l2 (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) m2 = Some (MPointer l')" using MTArray *** ** "*" MConArrayPointers gr_zeroI less_nat_zero_code by metis
    ultimately show "\<exists>l'. accessStore (hash l2 (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) m2 = Some (MPointer l') \<and> MCon (MTArray x1 t) m1 l \<and> MCon (MTArray x1 t) m2 l'" 
      using MTArray.IH ** ***
      by (meson "*" CompTypeRemainsMCon MTArray.prems(2) CompMemType.simps(2))

  next
    fix i1 i2 val
    assume *:"i1<x" and ***:"i2<x"
      and **:" accessStore (hash l1 (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) m1 = Some (MValue val)"
    show "\<exists>val'. accessStore (hash l2 (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) m2 = Some (MValue val') \<and> MCon (MTArray x1 t) m1 (hash l1 (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) \<and> MCon (MTArray x1 t) m2 (hash l2 (ShowL\<^sub>n\<^sub>a\<^sub>t i2))" 
      using "*" "**" MTArray.prems(1) by fastforce
  qed
next
  case (MTValue x')
  show ?case
  proof(intros)
    fix i1 i2 l 
    assume *:"i1<x" and ***:"i2<x" 
      and **:"accessStore (hash l1 (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) m1 = Some (MPointer l)"
    show "\<exists>l'. accessStore (hash l2 (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) m2 = Some (MPointer l') \<and> MCon (MTValue x') m1 l \<and> MCon (MTValue x') m2 l'" using * ** MTValue by auto
  next 
    fix i1 i2 val 
    assume *:"i1<x" and ****:"i2<x"
      and **:"accessStore (hash l1 (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) m1 = Some (MValue val)"
    have ***:"(case accessStore (hash l2 (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) m2 of None \<Rightarrow> False 
                 | Some (MValue val) \<Rightarrow> (case MTValue x' of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTValue x') m2 (hash l2 (ShowL\<^sub>n\<^sub>a\<^sub>t i2)))
                 | Some (MPointer loc2) \<Rightarrow> (case MTValue x' of MTArray len' arr' \<Rightarrow> MCon (MTValue x') m2 loc2 | MTValue Types \<Rightarrow> False))"
      using MTValue(2) MCon.simps(2)[of x "MTValue x'" m2 l2] * **** by simp
    then have "\<exists>l. accessStore (hash l2 (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) m2 = Some (MValue l)" 
      by (auto split:option.splits MTypes.splits Memoryvalue.splits)
    moreover have "MCon (MTValue x') m1 (hash l1 (ShowL\<^sub>n\<^sub>a\<^sub>t i1))" using * ** MTValue by auto 
    ultimately show "\<exists>val'. accessStore (hash l2 (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) m2 = Some (MValue val') \<and> MCon (MTValue x') m1 (hash l1 (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) 
                    \<and> MCon (MTValue x') m2 (hash l2 (ShowL\<^sub>n\<^sub>a\<^sub>t i2))" using *** by  auto
  qed
qed


lemma ReachableMem_Exists:
  assumes "x \<in> ReachableMem e sk mem"
  shows "\<exists>t l stack_loc mtype mem_loc. 
            (t, l) \<in> fset (fmran (denvalue e)) 
            \<and>l = Stackloc stack_loc
            \<and> t = Memory mtype
            \<and> accessStore stack_loc sk = Some (KMemptr mem_loc)
            \<and> x \<in> GetAllMemoryLocations mtype mem_loc mem" 
  using assms unfolding ReachableMem.simps
proof
  fix xa 
  assume a1:"xa |\<in>| fmran (denvalue e)"
    and  a2:"x \<in> (case xa of
                (t, Stackloc loc) \<Rightarrow>
                  (case accessStore loc sk of 
                    None \<Rightarrow> {}
                  | Some (KMemptr ptr) \<Rightarrow>
                      (case t of Memory struct \<Rightarrow> GetAllMemoryLocations struct ptr mem | _ \<Rightarrow> {})
                  | Some _ \<Rightarrow> {})
                | (t, Storeloc loc) \<Rightarrow> {})"
  then show "\<exists>t l stack_loc mtype mem_loc.
             (t, l) |\<in>| fmran (denvalue e) \<and>
             l = Stackloc stack_loc \<and>
             t = Memory mtype \<and>
             accessStore stack_loc sk = Some (KMemptr mem_loc) \<and>
             x \<in> GetAllMemoryLocations mtype mem_loc mem" using a1 
  proof(cases xa)
    case (Pair a b)
    then show ?thesis 
    proof(cases b)
      case (Stackloc x1)
      then have a3:"x \<in> (case accessStore x1 sk of None \<Rightarrow> {}
                  | Some (KMemptr ptr) \<Rightarrow>
                      (case a of Memory struct \<Rightarrow> GetAllMemoryLocations struct ptr mem | _ \<Rightarrow> {})
                  | Some _ \<Rightarrow> {})" using a2 Pair by auto
      then show ?thesis 
      proof(cases "accessStore x1 sk")
        case None
        then show ?thesis using a3 by simp
      next
        case (Some a')
        then show ?thesis 
        proof(cases a')
          case (KValue x1)
          then show ?thesis using a3 Some by simp
        next
          case (KCDptr x2)
          then show ?thesis using a3 Some by simp
        next
          case (KMemptr x3)
          then show ?thesis 
          proof(cases a)
            case (Value x1)
            then show ?thesis using a3 Some KMemptr by simp
          next
            case (Calldata x2)
            then show ?thesis using a3 Some KMemptr by simp
          next
            case (Memory x3')
            then have "x \<in> GetAllMemoryLocations x3' x3 mem"
              using a3 Some KMemptr by auto
            then show ?thesis using a1 Pair Stackloc Some KMemptr Memory by blast
          next
            case (Storage x4)
            then show ?thesis using a3 Some KMemptr by simp
          qed
        next
          case (KStoptr x4)
          then show ?thesis using a3 Some by simp
        qed
      qed
    next
      case (Storeloc x2)
      then show ?thesis using a1 a2 Pair by auto
    qed
  qed
qed

lemma ReachableMem_D:
  assumes "x \<in> ReachableMem e sk mem"
  obtains t l stack_loc mtype mem_loc
  where "(t, l) \<in> fset (fmran (denvalue e)) "
    and "l = Stackloc stack_loc"
    and "t = Memory mtype"
    and "accessStore stack_loc sk = Some (KMemptr mem_loc)"
    and "x \<in> GetAllMemoryLocations mtype mem_loc mem"
  using ReachableMem_Exists assms by blast

lemma ReachableMem_NoPtr_Change:
  assumes stack_ptrs_eq: "\<forall>l ptr.
        accessStore l (stack st) = Some (KMemptr ptr) \<longleftrightarrow>
        accessStore l (stack st') = Some (KMemptr ptr)"
    and memory_eq: "memory st = memory st'"
  shows "ReachableMem e (stack st) (memory st) = ReachableMem e (stack st') (memory st')"
proof
  show "ReachableMem e (stack st) (memory st) \<subseteq> ReachableMem e (stack st') (memory st')"
  proof
    fix x assume x_in_ReachableMem_st: "x \<in> ReachableMem e (stack st) (memory st)" 

    have a20:"\<forall>mtype mem_loc. GetAllMemoryLocations mtype mem_loc (memory st) 
                                = GetAllMemoryLocations mtype mem_loc (memory st')"
      using memory_eq by simp
    then obtain t l stack_loc mtype mem_loc 
      where o1:"(t, l) \<in> fset (fmran (denvalue e)) "
        and o2:"l = Stackloc stack_loc"
        and o3:"t = Memory mtype"
        and o4:"accessStore stack_loc (stack st) = Some (KMemptr mem_loc)"
        and o5:"x \<in> GetAllMemoryLocations mtype mem_loc (memory st)"  using ReachableMem_D x_in_ReachableMem_st by blast
    then have "accessStore stack_loc (stack st') = Some (KMemptr mem_loc)" using assms by blast
    moreover have "x \<in> GetAllMemoryLocations mtype mem_loc (memory st')" using a20 
      using \<open>x \<in> GetAllMemoryLocations mtype mem_loc (memory st)\<close> by auto

    ultimately have "x \<in> (\<Union>(t, y)\<in>fset (fmran (denvalue e)).
             case_Denvalue
              (\<lambda>loc. case accessStore loc (stack st') of None \<Rightarrow> {}
                      | Some (KMemptr ptr) \<Rightarrow>
                          (case t of Memory struct \<Rightarrow> GetAllMemoryLocations struct ptr (memory st') | _ \<Rightarrow> {})
                      | Some _ \<Rightarrow> {})
              (\<lambda>loc. {}) y)" using o1 o2 o3 by force
    then show "x \<in> ReachableMem e (stack st') (memory st')" unfolding ReachableMem.simps by blast

  qed
next 
  show "ReachableMem e (stack st') (memory st') \<subseteq> ReachableMem e (stack st) (memory st)"
  proof
    fix x assume x_in_ReachableMem_st: "x \<in> ReachableMem e (stack st') (memory st')" 

    have a20:"\<forall>mtype mem_loc. GetAllMemoryLocations mtype mem_loc (memory st) 
                                = GetAllMemoryLocations mtype mem_loc (memory st')"
      using memory_eq by simp
    then obtain t l stack_loc mtype mem_loc 
      where o1:"(t, l) \<in> fset (fmran (denvalue e)) "
        and o2:"l = Stackloc stack_loc"
        and o3:"t = Memory mtype"
        and o4:"accessStore stack_loc (stack st') = Some (KMemptr mem_loc)"
        and o5:"x \<in> GetAllMemoryLocations mtype mem_loc (memory st')"  using ReachableMem_D x_in_ReachableMem_st by blast
    then have "accessStore stack_loc (stack st) = Some (KMemptr mem_loc)" using assms by blast
    moreover have "x \<in> GetAllMemoryLocations mtype mem_loc (memory st)" using a20 
      using \<open>x \<in> GetAllMemoryLocations mtype mem_loc (memory st')\<close> by auto

    ultimately have "x \<in> (\<Union>(t, y)\<in>fset (fmran (denvalue e)).
             case_Denvalue
              (\<lambda>loc. case accessStore loc (stack st) of None \<Rightarrow> {}
                      | Some (KMemptr ptr) \<Rightarrow>
                          (case t of Memory struct \<Rightarrow> GetAllMemoryLocations struct ptr (memory st) | _ \<Rightarrow> {})
                      | Some _ \<Rightarrow> {})
              (\<lambda>loc. {}) y)" using o1 o2 o3 by force
    then show "x \<in> ReachableMem e (stack st) (memory st)" unfolding ReachableMem.simps by blast
  qed
qed

lemma SubPtrs_top:
  assumes "LSubPrefL2 stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc (memory st)))"
    and "\<forall>l l'. LSubPrefL2 l (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc (memory st))) \<and> accessStore l (memory st') = Some (MPointer l') \<longrightarrow> l' = l"
    and "TypedMemSubPrefPtrs (memory st') x11 x12 stl2 dloc1"
  shows "LSubPrefL2 dloc1 (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc (memory st)))" 
proof(cases x12)
  case (MTArray x11' x12')

  then obtain i l where idef:"i<x11 \<and> accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (memory st') = Some (MPointer l) \<and> (l = dloc1 \<or> TypedMemSubPrefPtrs (memory st') x11' x12' l dloc1)" 
    using assms by auto
  then have lsubloc:"LSubPrefL2 (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc (memory st)))" using  LSubPrefL2_def 
    using assms(1) hash_suffixes_associative by auto
  then have lSelfPoint:"l = (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using assms idef by simp

  have lsubloc:"LSubPrefL2 l (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc (memory st)))" using lsubloc lSelfPoint by simp

  then show ?thesis 
  proof(cases "l = dloc1")
    case True
    then show ?thesis 
      using lsubloc lSelfPoint by auto
  next
    case False
    then have lneq2:"\<forall>i<x11'. LSubPrefL2 (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc (memory st)))" using lSelfPoint idef lsubloc 
      by (metis LSubPrefL2_def Not_Sub_More_Specific)
    have "TypedMemSubPrefPtrs (memory st') x11' x12' l dloc1" using idef False by simp
    then show ?thesis using lneq2 lsubloc 
    proof(induction x12' arbitrary:x11' l)
      case (MTArray x1 x12')
      have "\<exists>i'<x11'. \<exists>l'. accessStore (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (memory st') = Some (MPointer l') \<and> (l' = dloc1 \<or> TypedMemSubPrefPtrs (memory st') x1 x12' l' dloc1)" 
        using MTArray(2) unfolding TypedMemSubPrefPtrs.simps by simp
      then obtain i' l' where i'def:"i'<x11' \<and> accessStore (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (memory st') = Some (MPointer l') \<and> (l' = dloc1 \<or> TypedMemSubPrefPtrs (memory st') x1 x12' l' dloc1)" by blast

      have l'subloc:"LSubPrefL2 (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc (memory st)))" using  i'def LSubPrefL2_def 
        using MTArray.prems(2) by auto
      then have l'SP:"(hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i')) = l'" using  i'def assms by auto
      show ?case 
      proof(cases "l' = dloc1")
        case True
        then show ?thesis using l'SP l'subloc by simp
      next
        case False
        then have "TypedMemSubPrefPtrs (memory st') x1 x12' l' dloc1" using i'def by simp
        moreover have "\<forall>i<x1. LSubPrefL2 (hash l' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (ShowL\<^sub>n\<^sub>a\<^sub>t(toploc (memory st)))" using l'subloc MemLSubPrefL2_specific_imps_general l'SP l'subloc 
          by (metis LSubPrefL2_def Not_Sub_More_Specific)
        ultimately show ?thesis using MTArray.IH[of x1 l']  l'subloc l'SP by blast
      qed
    next
      case (MTValue x)
      then show ?case by auto
    qed
  qed
next
  case (MTValue x2)
  then show ?thesis 
    using LSubPrefL2_def  hash_suffixes_associative  
    using assms(1,3) by auto
qed



lemma TypedMemSubPrefPtrs_imps_in_GetAllMemoryLocations_val:
  assumes "MCon (MTArray len2 arr2) mem stl2"
    and "TypedMemSubPrefPtrs mem len2 arr2 stl2 locs"
    and "\<exists>v. accessStore locs mem = Some (MValue v)"
  shows "locs \<in> GetAllMemoryLocations (MTArray len2 arr2) stl2 mem" using assms
proof (induction arr2 arbitrary: len2 stl2)
  case (MTArray x11 x12)
  then have "(\<exists>i<len2. \<exists>l. accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l) 
              \<and> (l = locs \<or> TypedMemSubPrefPtrs mem x11 x12 l locs))" 
    using assms(2) TypedMemSubPrefPtrs.simps(2)[of mem len2 x11 x12 stl2 locs] by blast
  then obtain i l where iDef:"i<len2 \<and> accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l) 
              \<and> (l = locs \<or> TypedMemSubPrefPtrs mem x11 x12 l locs)" by blast
  have "locs \<in> GetAllMemoryLocations (MTArray len2 (MTArray x11 x12)) stl2 mem" 
  proof(cases "l = locs")
    case True
    then have "\<exists>p. accessStore l mem = Some (MPointer p)" using MTArray  iDef 
      by (metis (lifting) MconSameTypeSameAccessWithTyping  option.discI MCon.simps(2))
    then show ?thesis using assms True by auto
  next
    case False
    then have "TypedMemSubPrefPtrs mem x11 x12 l locs" using iDef by auto
    moreover have "MCon (MTArray x11 x12) mem l" using iDef MTArray.prems(1) 
      using MCon_imps_sub_Mcon by blast
    ultimately have "locs \<in> GetAllMemoryLocations (MTArray x11 x12) l mem"
      using MTArray.IH[of x11 l] MTArray.prems(3) False iDef by blast
    then show ?thesis using GetAllMemoryLocations.simps iDef False by force
  qed
  then show ?case by auto
next
  case (MTValue x2)
  then have "(\<exists>i<len2. hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i) = locs)" 
    using assms(2) TypedMemSubPrefPtrs.simps(1)[of mem len2 x2 stl2 locs] by blast
  then obtain i where iDef:"i<len2 \<and> hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i) = locs" by blast
  then obtain v where vDef: "accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MValue v)" 
    using assms(1) MTValue MCon_sub_MTVal_imps_val by blast
  then have " locs \<in> GetAllMemoryLocations (MTArray len2 (MTValue x2)) stl2 mem" 
    unfolding GetAllMemoryLocations.simps using iDef vDef  by fastforce
  then show ?case using MTValue by auto
qed

lemma TypedMemSubPrefPtrs_trns:
  assumes "TypedMemSubPrefPtrs mem x2 t2 l2 l3"
    and "MCon (MTArray x t) mem l2"
    and "MCon (MTArray x1 t1) mem l1"
    and "CompMemType mem x1 t1 (MTArray x2 t2) l1 l2"
  shows "TypedMemSubPrefPtrs mem x1 t1 l1 l3" using assms
proof(induction t1 arbitrary:x1 l1)
  case (MTArray x1' t1')
  then have "(\<exists>i<x1. \<exists>l. accessStore (hash l1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l) \<and> (l = l2 \<and> MTArray x1' t1' = MTArray x2 t2 \<or> CompMemType mem x1' t1' (MTArray x2 t2) l l2))" 
    using CompMemType.simps(2)[of mem x1 x1' t1' "MTArray x2 t2" l1 l2] by auto
  then obtain i l where idef:"i<x1 \<and> accessStore (hash l1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l) \<and> (l = l2 \<and> MTArray x1' t1' = MTArray x2 t2 \<or> CompMemType mem x1' t1' (MTArray x2 t2) l l2)" 
    by blast
  then have mcond:"MCon (MTArray x1' t1') mem l" using MTArray(4) 
    using CompTypeRemainsMCon CompMemType.simps(2) by blast

  then show ?case using TypedMemSubPrefPtrs.simps(2)[of mem x1 x1' t1' l1 l3] idef 
    using MTArray.IH assms(1) assms(2) by blast
next
  case (MTValue x)
  then show ?case by simp
qed

lemma allocateMCon:
  assumes "MCon t mm loc"
    and "snd (allocate mm) = m'"
  shows "MCon t m' loc"
proof - 
  have "\<forall>locs. accessStore locs mm = accessStore locs m'" 
    using assms(2) unfolding allocate_def accessStore_def by auto
  then show ?thesis using assms(1)
  proof(induction t arbitrary:loc)
    case (MTArray x1 t)
    have old:"\<forall>i<x1.
          (case accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mm of None \<Rightarrow> False
           | Some (MValue val) \<Rightarrow> (case t of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon t mm (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
           | Some (MPointer loc2) \<Rightarrow> (case t of MTArray len' arr' \<Rightarrow> MCon t mm loc2 | MTValue val \<Rightarrow> False)) \<and>
          ((\<exists>p. accessStore loc mm = Some (MPointer p)) \<or> accessStore loc mm = None)"
      using MTArray.prems(2) unfolding MCon.simps by simp
    have "\<forall>i<x1.
            (case accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' of None \<Rightarrow> False
             | Some (MValue val) \<Rightarrow> (case t of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon t m' (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
             | Some (MPointer loc2) \<Rightarrow> (case t of MTArray len' arr' \<Rightarrow> MCon t m' loc2 | MTValue val \<Rightarrow> False))"
    proof intros
      fix i 
      assume *:"i<x1"
      then show "(case accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' of None \<Rightarrow> False
             | Some (MValue val) \<Rightarrow> (case t of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon t m' (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
             | Some (MPointer loc2) \<Rightarrow> (case t of MTArray len' arr' \<Rightarrow> MCon t m' loc2 | MTValue val \<Rightarrow> False))"
      proof(cases t)
        case mta:(MTArray x11 x12)
        then obtain v where vDef:"accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mm = Some (MPointer v)
                                  \<and> MCon t mm v" using * old 
            by (metis MConArrayPointers MCon_imps_sub_Mcon MTArray.prems(2) MCon.simps(2))
        then show ?thesis using * MTArray mta by fastforce
      next
        case (MTValue x2)
        then obtain v where vDef:"accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mm = Some (MValue v)
                                  \<and> MCon t mm (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using * old 
          using MCon_imps_sub_Mcon MCon_sub_MTVal_imps_val MTArray.prems(2) by presburger
        then show ?thesis using MTArray.prems(1) MTValue by auto
      qed
    qed
    then show ?case unfolding MCon.simps using MTArray.prems 
      by (metis MCon.simps(2))
  next
    case (MTValue x)
    then show ?case by simp
  qed
qed


lemma compMemTypes_trns:
  assumes "CompMemType mem len' arr' tp2 p' stl1"
    and "CompMemType mem len arr (MTArray len' arr') p'' p'"
  shows "CompMemType mem len arr tp2 p'' stl1" using assms
proof(induction arr arbitrary:p'' len)
  case (MTArray x1 arr)
  then show ?case by fastforce
next
  case (MTValue x)
  then show ?case by auto
qed

lemma cpm2mLessThanTopMemSame:
  assumes "(\<forall>i loc. i < toploc (memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<longrightarrow> accessStore loc (memory st) = accessStore loc m')"
    and "CompMemType (memory st) x11' x12' dt stl2 stl1"
    and "(\<forall>loc y. accessStore loc (memory st) = Some y \<longrightarrow> (\<exists>tloc<toploc (memory st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))"
  shows "CompMemType m' x11' x12' dt stl2 stl1" using assms
proof(induction x12' arbitrary:x11' stl2)
  case (MTArray x1 x12')
  then have "(\<exists>i<x11'. \<exists>l. accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (memory st) = Some (MPointer l) \<and> 
            (l = stl1 \<and> MTArray x1 x12' = dt \<or> CompMemType (memory st) x1 x12' dt l stl1))" 
    using CompMemType.simps(2)[of "memory st" x11' x1 x12' "dt" stl2 stl1] by blast
  then obtain i l where ldef:"i<x11' \<and> accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (memory st) = Some (MPointer l) \<and> 
            (l = stl1 \<and> MTArray x1 x12' = dt \<or> CompMemType (memory st) x1 x12' dt l stl1)" by blast
  then show ?case 
  proof(cases "l = stl1")
    case True
    then show ?thesis 
      by (metis (mono_tags, lifting) MTArray.IH ldef assms(1) assms(3) CompMemType.simps(2))
  next
    case False
    then show ?thesis using ldef 
      using MTArray.IH assms(1) assms(2) assms(3) by force
  qed
next
  case (MTValue x)
  then show ?case by auto
qed

lemma cpm2mLessThanTopTypedMem:
  assumes "MCon (MTArray x11' x12') mem stl2"
    and "(\<forall>i loc. i < toploc mem \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<longrightarrow> accessStore loc mem = accessStore loc m')"
    and "(\<forall>loc y. accessStore loc mem = Some y \<longrightarrow> (\<exists>tloc<toploc mem. LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))"
    and "stl1 \<noteq> stl2"
    and "TypedMemSubPrefPtrs m' x11' x12' stl2 stl1"
  shows "TypedMemSubPrefPtrs mem x11' x12' stl2 stl1" using assms(1,4,5)
proof(induction x12' arbitrary:x11' stl2)
  case (MTArray x1 x12')
  have mcon:"\<forall>i<x11'.
             (case accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem of None \<Rightarrow> False
              | Some (MValue val) \<Rightarrow> (case MTArray x1 x12' of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTArray x1 x12') mem (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
              | Some (MPointer loc2) \<Rightarrow> (case MTArray x1 x12' of MTArray len' arr' \<Rightarrow> MCon (MTArray x1 x12') mem loc2 | MTValue Types \<Rightarrow> False)) \<and>
             ((\<exists>p. accessStore stl2 mem = Some (MPointer p)) \<or> accessStore stl2 mem = None)" 
    using MTArray(2) MCon.simps(2)[of x11' "MTArray x1 x12'" mem stl2 ] by auto
  have "(\<exists>i<x11'. \<exists>l. accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MPointer l) \<and> (l = stl1 \<or> TypedMemSubPrefPtrs m' x1 x12' l stl1))" 
    using MTArray TypedMemSubPrefPtrs.simps(2)[of m' x11' x1 x12' stl2 stl1] by auto
  then obtain i l where idef:"i<x11' \<and> accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MPointer l)
                             \<and> (l = stl1 \<or> TypedMemSubPrefPtrs m' x1 x12' l stl1)" by blast
  then show ?case 
  proof(cases "l = stl1")
    case True
    then obtain l' where "accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l')" using idef mcon 
      using MConArrayPointers MTArray.prems(1) by blast
    then have "(\<exists>tloc<toploc mem. LSubPrefL2 (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (ShowL\<^sub>n\<^sub>a\<^sub>t tloc))" using assms by simp
    then show ?thesis using idef mcon True 
      by (metis assms(2) TypedMemSubPrefPtrs.simps(2))
  next
    case False
    then obtain l' where l'def:"accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l')" using idef mcon 
      using MConArrayPointers MTArray.prems(1) by blast
    then have "(\<exists>tloc<toploc mem. LSubPrefL2 (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (ShowL\<^sub>n\<^sub>a\<^sub>t tloc))" using assms by simp
    then have "l' = l" using idef l'def assms by auto 
    moreover have "TypedMemSubPrefPtrs m' x1 x12' l stl1" using False idef by auto
    moreover have "stl1 \<noteq> l" 
      using False by auto
    ultimately have "TypedMemSubPrefPtrs mem x1 x12' l stl1" using MTArray.IH[of x1 l ] mcon l'def  
      using idef by fastforce
    then show ?thesis using idef 
      using \<open>l' = l\<close> l'def by auto
  qed
next
  case (MTValue x)
  then show ?case by auto
qed






lemma existantSubLocs:
  assumes "MCon (MTArray x t) m1 l1"
    and "MCon (MTArray x t) m2 l2"
  shows "\<forall>l1'. TypedMemSubPrefPtrs m1 x t l1 l1' \<longrightarrow> (\<exists>l2' t'. TypedMemSubPrefPtrs m2 x t l2 l2' \<and> MCon t' m1 l1' \<and> MCon t' m2 l2')" using assms
proof(induction t arbitrary: x l2 l1)
  case (MTArray x1 t)
  show ?case 
  proof(intros)
    fix l1' 
    assume *:"TypedMemSubPrefPtrs m1 x (MTArray x1 t) l1 l1'"
    then have "(\<exists>i<x. \<exists>l. accessStore (hash l1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m1 = Some (MPointer l) \<and> (l = l1' \<or> TypedMemSubPrefPtrs m1 x1 t l l1'))"
      using TypedMemSubPrefPtrs.simps(2)[of m1 x x1 t l1 l1'] by blast
    then obtain i l where idef:"i<x \<and>  accessStore (hash l1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m1 = Some (MPointer l) \<and> (l = l1' \<or> TypedMemSubPrefPtrs m1 x1 t l l1')" by blast
    then have mcon1:"MCon (MTArray x1 t) m1 l" using MTArray(2) MCon.simps(2)[of x "MTArray x1 t" m1 l1] 
      using MCon_imps_sub_Mcon by blast
    then show "\<exists>l2' t'. TypedMemSubPrefPtrs m2 x (MTArray x1 t) l2 l2' \<and> MCon t' m1 l1' \<and> MCon t' m2 l2'" 
    proof(cases "l = l1'")
      case True

      then show ?thesis 
        by (metis MConArrayPointers MCon_imps_sub_Mcon MTArray.prems(2) gr_zeroI idef less_nat_zero_code mcon1 TypedMemSubPrefPtrs.simps(2))
    next
      case False
      then have "TypedMemSubPrefPtrs m1 x1 t l l1'" using idef by simp
      then obtain l2' where l2'_def:"accessStore (hash l2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m2 = Some (MPointer l2')" 
        using MTArray.prems(2) MCon.simps(2)[of x "MTArray x1 t" m2 l2] idef 
        by (metis MConArrayPointers)
      then have mcon2:"MCon (MTArray x1 t) m2 l2'" using MTArray.prems(2) MCon_imps_sub_Mcon 
        using idef by blast
      then have "\<exists>l2'' t'. TypedMemSubPrefPtrs m2 x1 t l2' l2'' \<and> MCon t' m1 l1' \<and> MCon t' m2 l2''"
        using MTArray.IH[of ] mcon1 mcon2 
        using False idef by blast
      then obtain l2'' t' where "TypedMemSubPrefPtrs m2 x1 t l2' l2'' \<and> MCon t' m1 l1' \<and> MCon t' m2 l2''" by blast
      then show ?thesis using l2'_def TypedMemSubPrefPtrs.simps(2)[of m2 x x1 t l2 l2''] idef by auto
    qed
  qed
next
  case (MTValue x')
  show ?case 
  proof(intros)
    fix l1'
    assume *:"TypedMemSubPrefPtrs m1 x (MTValue x') l1 l1'"
    then show "\<exists>l2' t'. TypedMemSubPrefPtrs m2 x (MTValue x') l2 l2' \<and> MCon t' m1 l1' \<and> MCon t' m2 l2' " 
      using MTValue 
      by (metis CompTypeRemainsMCon TypedMemSubPrefPtrs.simps(1) CompMemType.simps(1))
  qed
qed

lemma in_GetAllMemoryLocations_imps_TypedMemSubPrefPtrs:
  assumes "MCon (MTArray len2 arr2) mem stl2"
    and "locs \<in> GetAllMemoryLocations (MTArray len2 arr2) stl2 mem"
  shows "\<exists>locs' . accessStore locs mem = Some (MPointer locs') \<and> TypedMemSubPrefPtrs mem len2 arr2 stl2 locs' \<or> 
                 accessStore locs mem = Some (MValue locs') \<and> TypedMemSubPrefPtrs mem len2 arr2 stl2 locs" using assms
proof (induction arr2 arbitrary: len2 stl2 mem)
  case (MTArray x1 arr2)
  then have *:"\<forall>i<len2. \<exists>p. accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer p)" 
    by (metis MConArrayPointers bot_nat_0.not_eq_extremum not_less_zero)

  then obtain i where a1:"(i<len2 \<and> (locs =  hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<or> (\<exists>l. accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l) \<and> locs \<in> GetAllMemoryLocations (MTArray x1 arr2) l mem)))"
    using MTArray.prems unfolding GetAllMemoryLocations.simps by force

  then show ?case
  proof (cases "locs = hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)")
    case True
    then obtain locs' where "accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer locs')" using * a1 by blast
    moreover have "TypedMemSubPrefPtrs mem len2 (MTArray x1 arr2) stl2 locs'" 
      using True a1 calculation TypedMemSubPrefPtrs.simps(2)[of mem len2 x1 arr2 stl2 locs']  by blast
    ultimately show ?thesis using * True by blast
  next
    case False
    then obtain i l where *: "i < len2 \<and> accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l) \<and> locs \<in> GetAllMemoryLocations (MTArray x1 arr2) l mem"
      using a1 by auto
    have "MCon (MTArray x1 arr2) mem l"
      using MTArray(2) * MCon_imps_sub_Mcon by blast
    then have "\<exists>locs'.
       accessStore locs mem = Some (MPointer locs') \<and> TypedMemSubPrefPtrs mem x1 arr2 l locs' \<or>
       accessStore locs mem = Some (MValue locs') \<and> TypedMemSubPrefPtrs mem x1 arr2 l locs"
      using MTArray.IH[of x1 mem l] * by simp
    then show ?thesis using * unfolding TypedMemSubPrefPtrs.simps 
      by blast
  qed
next
  case (MTValue x)
  then have "\<forall>i<len2. \<exists>p. accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MValue p)" using MCon_sub_MTVal_imps_val by blast
  then show ?case using MTValue unfolding TypedMemSubPrefPtrs.simps by force
qed

lemma in_GetAllMemoryLocations_imps_TypedMemSubPrefPtrs2:
  assumes "MCon (MTArray len2 arr2) mem stl2"
    and "locs \<in> GetAllMemoryLocations (MTArray len2 arr2) stl2 mem"
    and "accessStore locs mem = Some (MPointer locs') \<and> TypedMemSubPrefPtrs mem len2 arr2 stl2 locs'"
  shows "\<exists>locs'' t a i. CompMemType mem len2 arr2 (MTArray t a) stl2 locs'' \<and> i< t \<and>locs = hash locs'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)
                         \<or> locs = hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<and> i<len2" using assms
proof (induction arr2 arbitrary: len2 stl2 mem)
  case (MTArray x1 arr2)
  then have *:"\<forall>i<len2. \<exists>p. accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer p)" 
    by (metis MConArrayPointers bot_nat_0.not_eq_extremum not_less_zero)

  then obtain i where a1:"(i<len2 \<and> (locs =  hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<or> (\<exists>l. accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l) \<and> locs \<in> GetAllMemoryLocations (MTArray x1 arr2) l mem)))"
    using MTArray.prems unfolding GetAllMemoryLocations.simps by fastforce

  then show ?case
  proof (cases "locs = hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)")
    case True
    then obtain locs' where "accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer locs')" using * a1 by blast
    moreover have "TypedMemSubPrefPtrs mem len2 (MTArray x1 arr2) stl2 locs'" 
      using True a1 calculation TypedMemSubPrefPtrs.simps(2)[of mem len2 x1 arr2 stl2 locs']  by blast
    ultimately show ?thesis using * True a1 by blast
  next
    case False
    then obtain i l where *: "i < len2 \<and> accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l) \<and> locs \<in> GetAllMemoryLocations (MTArray x1 arr2) l mem"
      using a1 by auto
    then have "accessStore locs mem = Some (MPointer locs') \<and> TypedMemSubPrefPtrs mem x1 arr2 l locs'" 
      using in_GetAllMemoryLocations_imps_TypedMemSubPrefPtrs[of x1 arr2 mem l locs] using MTArray.prems by auto
    moreover have "MCon (MTArray x1 arr2) mem l"
      using MTArray(2) * MCon_imps_sub_Mcon by blast
    ultimately have "\<exists>locs'' t a i. CompMemType mem x1 arr2 (MTArray t a) l locs'' \<and> i < t \<and> locs = hash locs'' (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<or> locs = hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<and> i < x1"
      using MTArray.IH[of x1 mem l] * by blast
    then show ?thesis using * unfolding TypedMemSubPrefPtrs.simps by fastforce
  qed
next
  case (MTValue x)
  then have "\<forall>i<len2. \<exists>p. accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MValue p)" using MCon_sub_MTVal_imps_val by blast
  then show ?case using MTValue unfolding TypedMemSubPrefPtrs.simps by force
qed


lemma intermediateLocation:
  assumes "(p' \<noteq> stl1 \<and> CompMemType mem x11 x12 tp2 p' stl1)"
    and "(stl1 \<noteq> p'' \<and> CompMemType mem x11' x12' (MTArray x t) p'' stl1)"
    and "\<not> TypedMemSubPrefPtrs mem x11' x12' p'' p'" 
    and "\<not> TypedMemSubPrefPtrs mem x11 x12 p' p''"
    and "MCon (MTArray x11 x12) mem p'"
    and "MCon (MTArray x11' x12') mem p''"
    and "p'' \<noteq> p'"
  shows "\<exists>initLoc intType intLen. TypedMemSubPrefPtrs mem x11 x12 p' initLoc \<and>TypedMemSubPrefPtrs mem x11' x12' p'' initLoc 
                                    \<and> ((TypedMemSubPrefPtrs mem  intLen intType initLoc stl1 \<and> stl1 \<noteq> initLoc) \<or> (stl1 = initLoc \<and> (MTArray x t) = (MTArray intLen intType)))" using assms
proof(induction x12 arbitrary:x11 x11' x12' p' p'')
  case (MTArray x1 x12)
  then show ?case 
    using CompMemType_imps_TypedMemSubPrefPtrs by blast
next
  case (MTValue x')
  then have a10:"(tp2 = MTValue x' \<and> (\<exists>i<x11. hash p' (ShowL\<^sub>n\<^sub>a\<^sub>t i) = stl1))" using CompMemType.simps(1)[of mem x11 x' tp2 p' stl1] by blast
  then show ?case using MTValue
  proof(induction x12') 
    case (MTArray x1 x12')
    then have "(\<exists>i<x11'. \<exists>l. accessStore (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l) 
      \<and> (l = stl1 \<and> MTArray x1 x12' = MTArray x t \<or> CompMemType mem x1 x12' (MTArray x t) l stl1))" 
      using CompMemType.simps(2)[of mem x11' x1 x12'  "MTArray x t"  p'' stl1] by simp
    then obtain i l where idef:"i<x11' \<and>accessStore (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l) 
      \<and>  (l = stl1 \<and> MTArray x1 x12' = MTArray x t \<or> CompMemType mem x1 x12' (MTArray x t) l stl1)" by blast
    then show ?case 
      using CompMemType_imps_TypedMemSubPrefPtrs MTArray.prems(3) MTValue.prems(1) by blast
  next
    case (MTValue x)
    then show ?case by auto
  qed
qed

lemma limitedMemoryChange:
  assumes "\<not>TypedMemSubPrefPtrs mem x t p'' prnt"
    and "p'' \<noteq> prnt"
    and "\<forall>locs. locs \<noteq> (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i)) \<longrightarrow> accessStore locs mem = accessStore locs mem'"
    and "\<exists>p. accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem' = Some (MPointer p)"
    and "MCon (MTArray x t) mem p''"
  shows "MCon (MTArray x t) mem' p''" using assms
proof (induction t arbitrary: x p'')
  case (MTArray x1 t)
  then have "x \<noteq> 0" using MCon.simps by blast
  moreover have "(\<exists>p. accessStore p'' mem' = Some (MPointer p)) \<or> accessStore p'' mem' = None"
  proof(cases "p'' = (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i))")
    case True
    then show ?thesis using MTArray by blast
  next
    case False
    then have "accessStore p'' mem = accessStore p'' mem'" using MTArray by simp
    then show ?thesis using MTArray MCon.simps \<open>x\<noteq>0\<close> by simp
  qed
  moreover have "\<forall>i<x. (case accessStore (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem' of None \<Rightarrow> False
                 | Some (MValue val) \<Rightarrow> (case (MTArray x1 t) of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTArray x1 t) mem' (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
                 | Some (MPointer loc2) \<Rightarrow> (case (MTArray x1 t) of MTArray len' arr' \<Rightarrow> MCon (MTArray x1 t) mem' loc2 | MTValue Types \<Rightarrow> False))"
  proof intros
    fix ii assume iiDef:"ii<x"
    show " case accessStore (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) mem' of None \<Rightarrow> False
         | Some (MValue val) \<Rightarrow> (case (MTArray x1 t) of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTArray x1 t) mem' (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t ii)))
         | Some (MPointer loc2) \<Rightarrow> (case (MTArray x1 t) of MTArray len' arr' \<Rightarrow> MCon (MTArray x1 t) mem' loc2 | MTValue Types \<Rightarrow> False)"
    proof(cases " (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) = (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i))")
      case True
      then have "p'' = prnt" using ShowLNatDot 
        using hash_injective by blast
      then show ?thesis using MTArray by simp
    next
      case False
      then have same:"accessStore (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) mem = accessStore (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) mem'" using MTArray by simp
      then obtain v where "accessStore (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) mem' = Some (MPointer v) \<and> MCon (MTArray x1 t) mem v" 
        using MTArray iiDef MCon_imps_sub_Mcon 
        by (metis MConArrayPointers bot_nat_0.not_eq_extremum calculation(1))
      then show ?thesis using MTArray.IH[of x1 v ] MTArray.prems iiDef same by fastforce
    qed
  qed
  ultimately show ?case  by simp
next
  case (MTValue x')
  then have "x \<noteq> 0" using MCon.simps by auto
  moreover have "(\<exists>p. accessStore p'' mem' = Some (MPointer p)) \<or> accessStore p'' mem' = None"
  proof(cases "p'' = (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i))")
    case True
    then show ?thesis using MTValue by blast
  next
    case False
    then have "accessStore p'' mem = accessStore p'' mem'" using MTValue by simp
    then show ?thesis using MTValue MCon.simps \<open>x\<noteq>0\<close> by simp
  qed
  moreover have "\<forall>i<x. (case accessStore (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem' of None \<Rightarrow> False
                 | Some (MValue val) \<Rightarrow> (case MTValue x' of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTValue x') mem' (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
                 | Some (MPointer loc2) \<Rightarrow> (case MTValue x' of MTArray len' arr' \<Rightarrow> MCon (MTValue x') mem' loc2 | MTValue Types \<Rightarrow> False))"
  proof intros
    fix ii assume iiDef:"ii<x"
    show " case accessStore (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) mem' of None \<Rightarrow> False
         | Some (MValue val) \<Rightarrow> (case MTValue x' of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTValue x') mem' (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t ii)))
         | Some (MPointer loc2) \<Rightarrow> (case MTValue x' of MTArray len' arr' \<Rightarrow> MCon (MTValue x') mem' loc2 | MTValue Types \<Rightarrow> False)"
    proof(cases " (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) = (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i))")
      case True
      then have "p'' = prnt" using ShowLNatDot 
        using hash_injective by blast
      then show ?thesis using MTValue by simp
    next
      case False
      then have same:"accessStore (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) mem = accessStore (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) mem'" using MTValue by simp
      then obtain v where "accessStore (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) mem' = Some (MValue v) \<and> MCon (MTValue x') mem (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t ii))" using MTValue 
          MCon_sub_MTVal_imps_val iiDef by (metis MCon_imps_sub_Mcon)
      then show ?thesis using same by auto
    qed
  qed
  ultimately show ?case using MCon.simps(2)[of x "MTValue x'" mem p''] by simp
qed

lemma mconCopySingle:
  assumes "\<forall>locs. \<not> LSubPrefL2 locs l \<longrightarrow> accessStore locs cd' = accessStore locs c''"
    and"\<forall>loc. LSubPrefL2 loc l \<longrightarrow> accessStore loc cd' = None"
    and "MCon struct cd' x2"
  shows "MCon struct c'' x2" using assms(3)
proof(induction struct arbitrary:x2)
  case (MTArray x1 struct')
  then show ?case 
  proof(cases "x1 = 0")
    case True
    then show ?thesis using MTArray by simp
  next
    case False
    then have a10:"\<forall>(i::nat)<x1.
             case accessStore (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) cd' of None \<Rightarrow> False
             | Some (MValue val) \<Rightarrow> (case struct' of MTValue typ \<Rightarrow> MCon struct' cd' (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) | _ \<Rightarrow> False)
             | Some (MPointer loc2) \<Rightarrow> (case struct' of MTArray len' arr' \<Rightarrow> MCon struct' cd' loc2 | MTValue Types \<Rightarrow> False)" 
      using MCon.simps(2)[of x1 struct' cd' x2] MTArray by simp
    have "\<forall>i<x1.
             case accessStore (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) c'' of None \<Rightarrow> False
             | Some (MValue val) \<Rightarrow> (case struct' of MTValue typ \<Rightarrow> MCon struct' c'' (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) | _ \<Rightarrow> False)
             | Some (MPointer loc2) \<Rightarrow> (case struct' of MTArray len' arr' \<Rightarrow> MCon struct' c'' loc2 | MTValue Types \<Rightarrow> False)" 
    proof intros
      fix i assume a20:"i<x1"
      then obtain x where xdef:"accessStore (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) cd' = Some x" using a10 by fastforce
      then have "\<not> LSubPrefL2 (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) l" using assms by auto
      then have same:"accessStore (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) c''  = Some x" using assms(1) xdef by simp
      then show " case accessStore (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i))  c'' of None \<Rightarrow> False
             | Some (MValue val) \<Rightarrow> (case struct' of MTValue typ \<Rightarrow> MCon struct' c'' (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) | _ \<Rightarrow> False)
             | Some (MPointer loc2) \<Rightarrow> (case struct' of MTArray len' arr' \<Rightarrow> MCon struct' c'' loc2 | MTValue Types \<Rightarrow> False)"
      proof(cases "x")
        case (MValue x1')
        then show ?thesis 
        proof(cases struct')
          case (MTArray x11 x12)
          then show ?thesis using a10 a20 xdef MValue by auto
        next
          case (MTValue x2')
          then have "MCon struct' cd' (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using a10 a20 xdef MValue by auto
          then show ?thesis using same MValue MTValue MTArray(1) by force
        qed
      next
        case (MPointer x2)
        then show ?thesis 
        proof(cases struct')
          case mtr:(MTArray x11 x12)
          then have "MCon struct' cd' x2" using a10 a20 xdef MPointer 
            by fastforce
          then show ?thesis using same MPointer MTArray(1) mtr 
            by fastforce
        next
          case (MTValue x2')
          then show ?thesis using a10 a20 xdef MPointer by auto
        qed
      qed

    qed
    moreover have "(\<exists>p. accessStore x2 c'' = Some (MPointer p)) \<or> accessStore x2 c'' = None" 
      by (metis (no_types, lifting) MTArray.prems LSubPrefL2_def assms(1) assms(2) hash_suffixes_associative option.case_eq_if MCon.simps(2))
    ultimately show ?thesis using MCon.simps(2)[of x1 struct' c'' x2] 
      using False by auto
  qed
next
  case (MTValue x)
  then have "(case accessStore x2 cd' of None \<Rightarrow> False 
            | Some (MValue t) \<Rightarrow> typeCon x t 
            | Some (MPointer t) \<Rightarrow> False)" 
    using MCon.simps(1)[of x cd' x2] by simp
  then obtain t where "accessStore x2  cd' = Some (MValue t)"
    by (simp split:option.splits Memoryvalue.splits)
  then have "\<not>LSubPrefL2 x2 l" using assms(2) by auto
  then show ?case using MTValue assms by simp
qed



lemma mcon_accessStore:
  assumes "MCon (MTArray len arr) cd loc"
    and "len > 0"
    and "i<len"
  obtains (1) loc2 len' arr'
  where "accessStore (hash loc  (ShowL\<^sub>n\<^sub>a\<^sub>t i)) cd = Some (MPointer loc2)"
    and "arr = MTArray len' arr'"
  | (2) val tp
  where "accessStore (hash loc  (ShowL\<^sub>n\<^sub>a\<^sub>t i)) cd  = Some (MValue val)"
    and "arr = MTValue tp"     
proof(cases "accessStore (hash loc  (ShowL\<^sub>n\<^sub>a\<^sub>t i)) cd")
  case None
  then show ?thesis using assms MCon.simps by auto
next
  case (Some a)
  then show ?thesis 
  proof(cases a)
    case (MValue x1)
    then show ?thesis
    proof(cases arr)
      case (MTArray x11 x12)
      then show ?thesis using Some MValue MCon.simps assms by auto
    next
      case (MTValue x2)
      then show ?thesis using Some MValue MCon.simps assms by (simp add: "2")
    qed
  next
    case (MPointer x2)
    then show ?thesis
    proof(cases arr)
      case (MTArray x11 x12)
      then show ?thesis using Some MPointer MCon.simps assms by (simp add: "1")
    next
      case (MTValue x2)
      then show ?thesis using Some MPointer MCon.simps assms by auto
    qed
  qed
qed

lemma SameMCon_imps_MConAccessSame:
  assumes "MCon t m1 l1"
    and "MCon t m2 l2" 
  shows "MConAccessSame l1 l2 t m1 m2" using assms
proof(induction t arbitrary: l1 l2)
  case (MTArray x1 t)
  show ?case  unfolding MConAccessSame.simps
  proof(intros)
    fix i1 i2 l
    assume *:"i1 <x1" and **:"i2<x1" and ***:" accessStore (hash l1 (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) m1 = Some (MPointer l)"
    then have "\<exists>l'. accessStore (hash l2 (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) m2 = Some (MPointer l')" using MTArray.prems(2) 
      by (metis MTArray.prems(1) MTypes.distinct(1) Memoryvalue.distinct(1) gr_zeroI less_nat_zero_code mcon_accessStore option.inject)
    then obtain l' where l'def:"accessStore (hash l2 (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) m2 = Some (MPointer l')" by blast
    moreover have "MCon t m1 l" using MTArray.prems(1) * *** 
      using MCon_imps_sub_Mcon by blast
    moreover have "MCon t m2 l'" using ** l'def MTArray.prems(2) 
      using MCon_imps_sub_Mcon by blast
    ultimately have "MConAccessSame l l' t m1 m2" using MTArray.IH[of l l'] using MTArray.prems *** * ** by simp
    then show "\<exists>l'. accessStore (hash l2 (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) m2 = Some (MPointer l') \<and> MConAccessSame l l' t m1 m2 " using l'def by simp
  qed
next
  case (MTValue x)
  then have mc1:" case accessStore l1 m1 of None \<Rightarrow> False | Some (MValue xb) \<Rightarrow> typeCon x xb | Some (MPointer t) \<Rightarrow> False" 
    unfolding MCon.simps by simp
  have mc2:"case accessStore l2 m2 of None \<Rightarrow> False | Some (MValue xb) \<Rightarrow> typeCon x xb | Some (MPointer t) \<Rightarrow> False" 
    using MTValue unfolding MCon.simps by simp
  have "\<exists>val. accessStore l1 m1 = Some (MValue val) \<and> (\<exists>val'. accessStore l2 m2 = Some (MValue val'))" 
    using mc2 mc1 by (auto split:option.splits Memoryvalue.splits)
  then show ?case unfolding MConAccessSame.simps by blast
qed

lemma MCon_imps_TypedMemSubPref_Some:
  assumes "TypedMemSubPref x' loc t"
    and "MCon t m loc"
    and "\<forall>l l'. TypedMemSubPref l loc t \<and> accessStore l m = Some (MPointer l') \<longrightarrow> l' = l"
  shows "\<exists>v. accessStore x' m = Some v"
  using assms 
proof(induction t arbitrary:loc)
  case (MTArray x1 t)
  then have typed_pref: "TypedMemSubPref x' loc (MTArray x1 t)" by simp
  then have a1:"(\<exists>i<x1. TypedMemSubPref x' (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t \<or> x' = hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i))" 
    using TypedMemSubPref.simps(2)[of x' loc x1 t] by simp
  then have "x1 > 0" using not_less_zero by auto
  then have mcon_array: "x1 > 0 \<and> (\<forall>j<x1. case accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t j)) m of
                                     None \<Rightarrow> False 
                                   | Some (MValue val) \<Rightarrow> (case t of MTValue typ \<Rightarrow> MCon t m (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t j)) | _ \<Rightarrow> False)
                                   | Some (MPointer loc2) \<Rightarrow> (case t of MTArray len' arr' \<Rightarrow> MCon t m loc2 | MTValue typ \<Rightarrow> False)) 
                        \<and> (\<exists>p. accessStore loc m = Some (MPointer p) \<or> accessStore loc m = None)"
    using MTArray.prems(2) MCon.simps(2)[of x1 t m loc] by simp
  then have som:"\<forall>j<x1. \<exists>v. accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t j)) m = Some v"
    using mcon_accessStore 
    by fastforce
  then show ?case 
  proof(cases "\<exists>i<x1. x' = hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)")
    case True
    then show ?thesis using som by blast
  next
    case False
    then obtain i where iDef:"i<x1 \<and> TypedMemSubPref x' (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t" using a1 by blast
    then obtain v where vDef: "accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some v" using som by blast
    then show ?thesis 
    proof(cases v)
      case (MValue x1)
      then show ?thesis using iDef MTArray.IH vDef mcon_array 
        by (metis MTArray.prems(2) Memoryvalue.simps(4) TypedMemSubPref.simps(1) mcon_accessStore option.inject)
    next
      case (MPointer x2)
      then have "x2 = (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using iDef MTArray.prems(3) 
        using TypedMemSubPref.simps(2) vDef by blast
      then show ?thesis using MTArray.IH iDef vDef mcon_array 
        by (metis MCon_imps_sub_Mcon MPointer MTArray.prems(2,3) TypedMemSubPref.simps(2))
    qed
  qed
next
  case (MTValue x)
  then show ?case 
    by (metis MConAccessSame.simps(1) SameMCon_imps_MConAccessSame TypedMemSubPref.simps(1))
qed

(*
 Helper function to find all memory locations for a given memory type.
 It takes the type, a starting location, and the current memory state
 to resolve pointers.
*)
lemma mcon_typedptrs_ims_existance:
  assumes "MCon (MTArray x t) m1 l1"
  shows "\<forall>l1'. TypedMemSubPrefPtrs m1 x t l1 l1' \<longrightarrow> (\<exists>t. MCon t m1 l1')" using assms(1) 
proof(induction t arbitrary:x l1)
  case (MTArray x1 t)
  then show ?case 
    by (metis MCon_imps_sub_Mcon TypedMemSubPrefPtrs.simps(2))
next
  case (MTValue x)
  then show ?case 
    using CompTypeRemainsMCon TypedMemSubPrefPtrs.simps(1) CompMemType.simps(1) by blast
qed

lemma memSet_selfPoint:
  assumes "MCon t' m tL"
    and "x'' \<in> GetAllMemoryLocations t' tL m"
    and "\<forall>l l'. TypedMemSubPref l tL t' \<and> accessStore l m = Some (MPointer l') \<longrightarrow> l' = l"
    and "accessStore x'' m = Some (MPointer locs')"
  shows "locs' = x''" using assms
proof(induction t' arbitrary:tL)
  case (MTArray x1 t')
  obtain i where idef: "i\<in>{0..<x1} \<and> x'' \<in> (case accessStore (hash tL (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m of None \<Rightarrow> {} | Some (MValue xa) \<Rightarrow> {hash tL (ShowL\<^sub>n\<^sub>a\<^sub>t i)} \<union> GetAllMemoryLocations t' (hash tL (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m
           | Some (MPointer ptr) \<Rightarrow> {hash tL (ShowL\<^sub>n\<^sub>a\<^sub>t i)} \<union> GetAllMemoryLocations t' ptr m)" 
    using MTArray.prems unfolding GetAllMemoryLocations.simps by blast
  then consider (ptr) ptr where "i<x1 \<and> accessStore (hash tL (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some (MPointer ptr) \<and> x'' \<in> {hash tL (ShowL\<^sub>n\<^sub>a\<^sub>t i)} \<union> GetAllMemoryLocations t' ptr m"
    | (val) val where "i<x1 \<and> accessStore (hash tL (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some (MValue val) \<and> x'' \<in> {hash tL (ShowL\<^sub>n\<^sub>a\<^sub>t i)} \<union> GetAllMemoryLocations t' (hash tL (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m" 
    by (auto split:option.splits Memoryvalue.splits)
  then show ?case 
  proof(cases)
    case ptr
    then have subL:"TypedMemSubPref (hash tL (ShowL\<^sub>n\<^sub>a\<^sub>t i)) tL (MTArray x1 t')" by auto
    then have ptrSame:"ptr = (hash tL (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using MTArray.prems(3) ptr by blast

    then show ?thesis
    proof(cases "x'' = hash tL (ShowL\<^sub>n\<^sub>a\<^sub>t i)")
      case True
      then show ?thesis 
        using MTArray.prems(3) assms(4) subL by blast
    next
      case False
      then have a0:"x'' \<in> GetAllMemoryLocations t' ptr m" using ptr by simp
      moreover have "MCon t' m ptr" using MTArray.prems(1) ptr 
        using MCon_imps_sub_Mcon by blast
      moreover have "\<forall>l l'. TypedMemSubPref l ptr t' \<and> accessStore l m = Some (MPointer l') \<longrightarrow> l' = l" 
        using MTArray.prems(3) ptr ptrSame by auto
      ultimately have "locs' = x''" using MTArray.IH[OF _ a0] MTArray.prems(4)  by blast
      then show ?thesis by blast
    qed
  next
    case val
    then have "\<exists>v'. t' = MTValue v'" using MTArray.prems(1) 
      by (metis Memoryvalue.distinct(1) mcon_accessStore neq0_conv option.inject order_less_trans)
    then have "x'' = hash tL (ShowL\<^sub>n\<^sub>a\<^sub>t i)" using val by auto
    then show ?thesis using MTArray val by auto
  qed
next
  case (MTValue x)
  then show ?case by auto
qed


lemma moreSpecificTypedSubPref:
  assumes "( \<forall>l l'. TypedMemSubPref l destl (MTArray x t) \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l)"
  shows "\<forall>i<x. ( \<forall>l l'. TypedMemSubPref l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l)" using assms(1)
proof (induction t arbitrary:x)
  case (MTArray x1 t)
  show ?case 
  proof intros
    fix i l l'
    assume *:"i<x"
      and **:"TypedMemSubPref l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (MTArray x1 t) \<and> accessStore l v' = Some (MPointer l')"
    have b10:"TypedMemSubPref l destl (MTArray x (MTArray x1 t)) \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l" using MTArray by metis
    then show "l' =l" using  MTArray(1) b10 * **
      by (meson TypedMemSubPref.simps(2))
  qed
next
  case (MTValue x)
  then show ?case by auto
qed

lemma MCon_nonSub_selfPointing:
  assumes "(\<not>LSubPrefL2 destl'  destl) \<and> \<not>LSubPrefL2 destl  destl' "
  shows  "(\<forall>l l'. TypedMemSubPref l destl' t' \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l)
          \<and> (\<forall>destl'. \<not> LSubPrefL2 destl' destl \<longrightarrow> accessStore destl' v' = accessStore destl' v'')
          \<and> MCon t' v' destl' \<longrightarrow> MCon t' v'' destl'" using assms
proof(induction t' arbitrary:destl' )
  case (MTArray x1 t)
  show ?case 
  proof intros
    assume "(\<forall>l l'. TypedMemSubPref l destl' (MTArray x1 t) \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l) 
              \<and> (\<forall>destl'. \<not> LSubPrefL2 destl' destl \<longrightarrow> accessStore destl' v' = accessStore destl' v'')
              \<and> MCon (MTArray x1 t)  v' destl' 
              "
    then have *:"(\<forall>l l'. TypedMemSubPref l destl' (MTArray x1 t) \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l)"
      and **: "MCon (MTArray x1 t) v' destl'" 
      and ***:"(\<forall>destl'. \<not> LSubPrefL2 destl' destl \<longrightarrow> accessStore destl' v' = accessStore destl' v'')"
      by blast+


    then show "MCon  (MTArray x1 t)  v'' destl'"
    proof (cases "x1>0")
      case True
      have a10:"\<forall>i<x1.
             case accessStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i))  v'  of None \<Rightarrow> False 
              | Some (MValue val) \<Rightarrow> (case t of  MTValue typ \<Rightarrow> MCon  t v' (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) | _ \<Rightarrow> False)
             | Some (MPointer loc2) \<Rightarrow> (case t of MTArray len' arr' \<Rightarrow> MCon t v' loc2 | MTValue Types \<Rightarrow> False)" 
        using ** by auto


      have "\<forall>i<x1.
             case accessStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' of None \<Rightarrow> False 
              | Some (MValue val) \<Rightarrow> (case t of  MTValue typ \<Rightarrow> MCon t  v'' (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) | _ \<Rightarrow> False)
             | Some (MPointer loc2) \<Rightarrow> (case t of MTArray len' arr' \<Rightarrow> MCon t  v'' loc2 | MTValue Types \<Rightarrow> False)"
      proof intros
        fix i 
        assume iLess: "i<x1"
        show "case accessStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i))  v'' of None \<Rightarrow> False 
                  | Some (MValue val) \<Rightarrow> (case t of  MTValue typ \<Rightarrow> MCon t v'' (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) | _\<Rightarrow> False)
                  | Some (MPointer loc2) \<Rightarrow> (case t of MTArray len' arr' \<Rightarrow> MCon t  v'' loc2 | MTValue Types \<Rightarrow> False)"
        proof(cases t)
          case mtr:(MTArray x11 x12)
          have b100:"\<not> LSubPrefL2 (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) destl" using Mutual_NonSub_SpecificNonSub MTArray by auto
          then have "\<not> LSubPrefL2 destl (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using Not_Sub_More_Specific MTArray by auto
          then have a50:"(\<forall>l l'. TypedMemSubPref l (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l) 
                          \<and> (\<forall>destl'. \<not> LSubPrefL2 destl' destl \<longrightarrow> accessStore destl' v' = accessStore destl' v'')
                          \<and> MCon t v' (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) \<longrightarrow>
                          MCon t v'' (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i))
            " using MTArray(1)[of "(hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i))"] b100 hash_suffixes_associative by blast
          have a55:"\<forall>l l'. TypedMemSubPref l (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l" using * moreSpecificTypedSubPref[of destl' x1 t v'] iLess by blast
          then have a60:"accessStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = accessStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v''" using b100 *** by blast
          then show ?thesis
          proof(cases "accessStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'")
            case None
            then show ?thesis using a10 iLess by auto
          next
            case (Some a)
            then show ?thesis 
            proof(cases a)
              case (MValue x1)
              then show ?thesis using a10 iLess mtr Some by auto
            next
              case (MPointer x2')
              then have x2'def:"x2' = (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using a55 Some * 
                using iLess TypedMemSubPref.simps(2) by blast
              then have "MCon t v' (x2')" using a10 iLess Some mtr MPointer 
                by fastforce
              then have "MCon t v'' x2'" using a50 b100 a55 *** x2'def by auto
              then show ?thesis  using Some MPointer mtr a60 by auto
            qed
          qed
        next
          case (MTValue x2)
          have b100:"\<not> LSubPrefL2 (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) destl" using Mutual_NonSub_SpecificNonSub MTArray by auto
          then have "\<not> LSubPrefL2 destl (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using Not_Sub_More_Specific MTArray by auto
          then have a50:"(\<forall>destl'. \<not> LSubPrefL2 destl' destl \<longrightarrow> accessStore destl' v' = accessStore destl' v'') \<and>
                           MCon t v' (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) \<longrightarrow>
                          MCon t v'' (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i))
            " using MTArray(1)[of "(hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i))"] b100  using MTValue by force
          then have a60:"accessStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = accessStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v''" using b100 *** by simp
          then show ?thesis
          proof(cases "accessStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'")
            case None
            then show ?thesis using a10 iLess by auto
          next
            case (Some a)
            then show ?thesis 
            proof(cases a)
              case (MValue x1)
              then have "MCon t v' (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using a10 iLess Some MTValue by auto
              then have "MCon t v'' (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using a50 b100 a60 *** Some MValue by auto
              then show ?thesis using Some MValue MTValue a60 by auto
            next
              case (MPointer x2')
              then show ?thesis using a10 iLess MTValue Some by auto
            qed

          qed

        qed

      qed

      moreover have "(\<exists>p. accessStore destl' v'' = Some (MPointer p)) \<or> accessStore destl' v'' = None" using ** MCon.simps(2) 
        using MTArray.prems True \<open>(\<forall>l l'. TypedMemSubPref l destl' (MTArray x1 t) \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l) \<and> (\<forall>destl'. \<not> LSubPrefL2 destl' destl \<longrightarrow> accessStore destl' v' = accessStore destl' v'') \<and> MCon (MTArray x1 t) v' destl'\<close> by auto
      ultimately show ?thesis using MCon.simps(2)[of x1 t v'' destl']
        by (simp add: True)
    next
      case False
      then show ?thesis using ** by simp
    qed

  qed
next
  case (MTValue x)
  show ?case 
  proof intros
    assume "(\<forall>l l'. TypedMemSubPref l destl' (MTValue x) \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l) \<and>
    (\<forall>destl'. \<not> LSubPrefL2 destl' destl \<longrightarrow> accessStore destl' v' = accessStore destl' v'') \<and> 
MCon (MTValue x) v' destl' "
    then have *:"(\<forall>destl'. \<not> LSubPrefL2 destl' destl \<longrightarrow> accessStore destl' v' = accessStore destl' v'')"
      and **:"MCon (MTValue x) v' destl'" 
      and ***:"(\<forall>l len tp.
        MTValue x = MTArray len tp \<and> MCon (MTValue x) v' destl' \<longrightarrow>
        (\<forall>i<len. accessStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = Some (MPointer l) \<and> l = hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)))"
      by auto+
    then have "accessStore destl' v' = accessStore destl' v''" using MTValue by simp
    then show "MCon (MTValue x) v'' destl'"  using ** by simp
  qed
qed


lemma mtype_size_positive: "mtype_size t > 0"
  by (induction t rule: MTypes.induct) simp_all

lemma mtype_size_strict_decrease_array: "mtype_size arr < mtype_size (MTArray len arr)"
  by (simp)

subsection \<open>Memory and Calldata conformity\<close>
text \<open>The following function ensures that sub locations within a given memory or calldata conform 
      to their associated data types.
      Starting at a location (loc) this function searches all sub locations. 
      In the case of an array all further sublocation are checked. In the case of an MTvalue
      The string stored at the location is checked against its base datatype.\<close>
  (*There is an implicit assumption that the locations in the denvalue (which are the locations passed as loc in TypeSafe)
  already point to the MPointer location. This is the same logic used by msel.
I.e. If there is an MTArray at location 0.0 in storage with a pointer location value of 7.7 then the location stored for a reference to this
array in denvalue would be 7.7
This means that the location does not need to be looked up when passed in to the MCon function*)
  (*Assert that the length of an array must be greater than 0. This makes sense as memory arrays are fixed size and so 
there cannot be an array of length < 0 in solidity,m if len is zero then the array exists but has no values --Currently return false. thus True*)
lemma neg_MemLSubPrefL2_imps_TypedMemSubPref:
  assumes "\<not>LSubPrefL2 l1 l2"
  shows "\<not>TypedMemSubPref l1 l2 t" using assms
proof(induction t arbitrary:l2)
  case (MTArray x1 t)
  then show ?case 
    by (simp add: LSubPrefL2_def hash_suffixes_associative)
next
  case (MTValue x)
  then show ?case  
    by (simp add: LSubPrefL2_def)
qed

abbreviation mymemory::MemoryT
  where "mymemory \<equiv>
    \<lparr>mapping = fmap_of_list
      [(STR ''1.1.0'', MValue STR ''False''),
       (STR ''0.1.0'', MValue STR ''True''),
       (STR ''1.0'', MPointer STR ''1.0''),
       (STR ''1.0.0'', MValue STR ''False''),
       (STR ''0.0.0'', MValue STR ''True''),
       (STR ''0.0'', MPointer STR ''0.0'')],
     toploc = 1\<rparr>"
    
lemma reversable_CompMemJustType_imps_same:
  assumes "CompMemJustType t1 t2"
    and "CompMemJustType t2 t1"
  shows "t1 = t2"
  using assms
proof (induction t1 arbitrary: t2)
  case (MTValue tp)
  then show ?case by simp
next
  case (MTArray len arr)
  then obtain len2 arr2 where a10:"t2 = MTArray len2 arr2"
    using CompMemJustType.simps 
    by (metis MTypes.exhaust)

  then show ?case
  proof(cases "len2 = len \<and> arr2 = arr")
    case True
    then show ?thesis using a10 by auto
  next
    case False
    then have "CompMemJustType arr arr2" 
      using MTArray.prems(1) a10
      by (metis CompMemTypes_asc MTypes.exhaust MTypes.inject(1) CompMemJustType.simps(1) CompMemJustType.simps(2))
    moreover have "CompMemJustType arr2 arr" using a10 MTArray.prems False 
      by (metis CompMemJustType.simps(1,2) CompMemTypes_asc less_not_refl mtype_size.cases mtype_size_strict_decrease_array)
    ultimately have "arr = arr2"
      using MTArray.IH by auto
    then show ?thesis using MTArray \<open>CompMemJustType arr2 arr\<close> \<open>t2 = MTArray len2 arr2\<close> by force
  qed
qed



lemma CompMemTypeSameLocsSameType:
  assumes "MCon (MTArray len arr) mem p'"
    and "CompMemType mem len arr tp1 p' stl1"
    and "CompMemType mem len arr tp2 p' stl1"
  shows "tp2 = tp1" using assms
proof (induction arr arbitrary:len  p')
  case (MTArray x1 arr)
  then have a10:"(\<exists>i<len. \<exists>l. accessStore (hash p' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l) \<and> (l = stl1 \<and> MTArray x1 arr = tp1 \<or> CompMemType mem x1 arr tp1 l stl1))" 
    using CompMemType.simps(2)[of mem len x1 arr tp1 p' stl1] by auto
  have a20:"(\<exists>i<len. \<exists>l. accessStore (hash p' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l) \<and> (l = stl1 \<and> MTArray x1 arr = tp2 \<or> CompMemType mem x1 arr tp2 l stl1))"
    using MTArray.prems(3) by auto
  then obtain i l where ldef:"i<len \<and> accessStore (hash p' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l) 
                                    \<and> (l = stl1 \<and> MTArray x1 arr = tp1 \<or> CompMemType mem x1 arr tp1 l stl1) 
                                    \<and> (l = stl1 \<and> MTArray x1 arr = tp2 \<or> CompMemType mem x1 arr tp2 l stl1)"   
    by (smt (verit, ccfv_threshold) CompMemJustType.simps(1,2) CompMemJustTypes_trns 
             CompMemType_imps_CompMemJustType CompTypeRemainsMCon MConSubTypes MTArray.prems(1,2,3) extractType.cases)
    (*by (metis CompMemJustType.simps(1,2) CompMemJustTypes_trns CompMemType.simps(2) CompMemType_imps_CompMemJustType CompTypeRemainsMCon MConSubTypes
        MTArray.prems(1,2) mtype_size.cases)*)
  then show ?case 
  proof(cases "l = stl1")
    case True
    then have "\<not> CompMemType mem x1 arr tp1 l l" using BothMConImpsNotCompMemType[of x1 arr mem l tp1]  
      by (metis CompTypeRemainsMCon MTArray.prems(1) ldef CompMemType.simps(2))
    then show ?thesis using True a10 a20 ldef 
      by (metis BothMConImpsNotCompMemType CompTypeRemainsMCon MTArray.prems(1) MTArray.prems(2))
  next
    case False
    then have "CompMemType mem x1 arr tp1 l stl1" using ldef by auto
    moreover have "CompMemType mem x1 arr tp2 l stl1" using False ldef by simp
    ultimately show ?thesis using MTArray.IH a10 ldef MTArray.prems by auto
  qed
next
  case (MTValue x)
  then show ?case by simp
qed

lemma CompMemType_asc_withSharedTarget:
  assumes "CompMemType mem len x (MTArray x' t') p' stl2"
    and "CompMemType mem len x tp1 p' stl1"
    and "MCon (MTArray len x) mem p'"
    and "MCon tp1 mem stl1"
    and "MCon (MTArray x' t') mem stl2"
    and "TypedMemSubPrefPtrs mem x' t' stl2 stl1" 
  shows "CompMemType mem  x' t' tp1 stl2 stl1" using assms(1,3,4,5,6)
proof(induction t' arbitrary:stl2 x')
  case (MTArray x1 t')
  have "(\<exists>i<x'. \<exists>l. accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l) 
        \<and> (l = stl1 \<or> TypedMemSubPrefPtrs mem x1 t' l stl1))"
    using MTArray TypedMemSubPrefPtrs.simps(2)[of mem x' x1 t' stl2 stl1] by simp
  then obtain i l where idef:"i<x'" and ldef:"accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l) \<and> (l = stl1 \<or> TypedMemSubPrefPtrs mem x1 t' l stl1)" by blast
  have MConexpand:" \<forall>i<x'.
             (case accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem of None \<Rightarrow> False 
              | Some (MValue val) \<Rightarrow> (case MTArray x1 t' of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTArray x1 t') mem (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
              | Some (MPointer loc2) \<Rightarrow> (case MTArray x1 t' of MTArray len' arr' \<Rightarrow> MCon (MTArray x1 t') mem loc2 | MTValue Types \<Rightarrow> False)) \<and>
             ((\<exists>p. accessStore stl2 mem = Some (MPointer p)) \<or> accessStore stl2 mem = None)" using MTArray.prems MCon.simps(2)[of x' "(MTArray x1 t')" mem stl2] by simp
  have " (accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l) \<and> (l = stl1 \<and> MTArray x1 t' = tp1 \<or> CompMemType mem x1 t' tp1 l stl1))" 
  proof(cases "l = stl1")
    case True
    then show ?thesis 
      by (metis CompMemTypeSameLocsSameType MTArray.prems(1) assms(2) assms(3) compMemTypes_trns idef ldef CompMemType.simps(2))
  next
    case False
    then have "TypedMemSubPrefPtrs mem x1 t' l stl1" using ldef by simp
    then show ?thesis 
      by (meson CompTypeRemainsMCon MTArray.IH MTArray.prems(1) assms(2) assms(3) compMemTypes_trns idef ldef CompMemType.simps(2))
  qed
  then show ?case using CompMemType.simps(2)[of mem x' x1 t' tp1 stl2 stl1] idef ldef  by blast
next
  case (MTValue x)
  then show ?case 
    by (metis CompMemTypeSameLocsSameType TypedMemSubPrefPtrs.simps(1) assms(2) compMemTypes_trns CompMemType.simps(1))
qed

lemma CompMemType_asc_withSharedTarget2:
  assumes "CompMemType mem len x (MTArray x' t') p'' stl2"
    and "CompMemType mem len'' x'' tp1 p' stl1"
    and "CompMemType mem len x (MTArray len'' x'') p'' p'"
    and "MCon (MTArray len x) mem p''"
    and "TypedMemSubPrefPtrs mem x' t' stl2 stl1" 
    and "MCon (MTArray x' t') mem stl2"
  shows "CompMemType mem  x' t' tp1 stl2 stl1" using assms(1,2,3,4,5,6)
proof(induction t' arbitrary:stl2 x')
  case (MTArray x1 t')
  have "(\<exists>i<x'. \<exists>l. accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l) \<and> (l = stl1 \<or> TypedMemSubPrefPtrs mem x1 t' l stl1))"
    using MTArray TypedMemSubPrefPtrs.simps(2)[of mem x' x1 t' stl2 stl1] by simp
  then obtain i l where idef:"i<x'" and ldef:"accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l) \<and> (l = stl1 \<or> TypedMemSubPrefPtrs mem x1 t' l stl1)" by blast
  have MConexpand:" \<forall>i<x'.
             (case accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem of None \<Rightarrow> False 
              | Some (MValue val) \<Rightarrow> (case MTArray x1 t' of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTArray x1 t') mem (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
              | Some (MPointer loc2) \<Rightarrow> (case MTArray x1 t' of MTArray len' arr' \<Rightarrow> MCon (MTArray x1 t') mem loc2 | MTValue Types \<Rightarrow> False)) \<and>
             ((\<exists>p. accessStore stl2 mem = Some (MPointer p)) \<or> accessStore stl2 mem = None)" using MTArray.prems MCon.simps(2)[of x' "(MTArray x1 t')" mem stl2] by simp
  have " (accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l) \<and> (l = stl1 \<and> MTArray x1 t' = tp1 \<or> CompMemType mem x1 t' tp1 l stl1))" 
  proof(cases "l = stl1")
    case True
    then show ?thesis using MTArray 
      by (metis CompMemTypeSameLocsSameType compMemTypes_trns idef ldef CompMemType.simps(2))
  next
    case False
    then have "TypedMemSubPrefPtrs mem x1 t' l stl1" using ldef by simp
    then show ?thesis using MTArray 
      by (metis CompTypeRemainsMCon compMemTypes_trns idef ldef CompMemType.simps(2))

  qed
  then show ?case using CompMemType.simps(2)[of mem x' x1 t' tp1 stl2 stl1] idef ldef  by blast
next
  case (MTValue x)
  then have "(tp1 = MTValue x \<and> (\<exists>i<x'. hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i) = stl1))" 
    by (metis CompMemTypeSameLocsSameType TypedMemSubPrefPtrs.simps(1) compMemTypes_trns CompMemType.simps(1))
  then show ?case using CompMemType.simps(1)[of mem x' x tp1 stl2 stl1] by simp
qed



lemma TypedMemSubPrefOneWay:
  assumes "TypedMemSubPrefPtrs mem x1 t1 stl1 stl2"
    and "CompMemJustType (MTArray x1 t1) (MTArray x2 t2)"
    and "MCon (MTArray x1 t1) mem stl1"
    and "MCon (MTArray x2 t2) mem stl2"
    and "CompMemType mem x1 t1 (MTArray x2 t2) stl1 stl2"
  shows "\<not>TypedMemSubPrefPtrs mem x2 t2 stl2 stl1"
  using assms
proof(induction t2 arbitrary:x2 stl2)
  case (MTArray x2' t2')
  then show ?case 
  proof(induction t1 arbitrary: x1 stl1)
    case (MTArray x1' t1')
    show ?case 
    proof
      assume *:"TypedMemSubPrefPtrs mem x2 (MTArray x2' t2') stl2 stl1"
      then have a10:"(\<exists>i<x2. \<exists>l. accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l) \<and> (l = stl1 \<or> TypedMemSubPrefPtrs mem x2' t2' l stl1))" 
        using TypedMemSubPrefPtrs.simps(2)[of mem x2 x2' t2' stl2 stl1] by simp
      have a20:"(\<exists>i<x1. \<exists>l. accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l) \<and> (l = stl2 \<or> TypedMemSubPrefPtrs mem x1' t1' l stl2))" 
        using MTArray(3) TypedMemSubPrefPtrs.simps(2)[of mem x1 x1' t1' stl1 stl2] by simp
      have a30:"\<forall>i<x1.
             (case accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem of None \<Rightarrow> False
              | Some (MValue val) \<Rightarrow> (case MTArray x1' t1' of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTArray x1' t1') mem (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
              | Some (MPointer loc2) \<Rightarrow> (case MTArray x1' t1' of MTArray len' arr' \<Rightarrow> MCon (MTArray x1' t1') mem loc2 | MTValue Types \<Rightarrow> False)) 
            \<and> ((\<exists>p. accessStore stl1 mem = Some (MPointer p)) \<or> accessStore stl1 mem = None)" 
        using MTArray MCon.simps(2)[of x1 "MTArray x1' t1'" mem stl1] by simp
      have a40:"\<forall>i<x2.
             (case accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem of None \<Rightarrow> False
              | Some (MValue val) \<Rightarrow> (case MTArray x2' t2' of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTArray x2' t2') mem (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
              | Some (MPointer loc2) \<Rightarrow> (case MTArray x2' t2' of MTArray len' arr' \<Rightarrow> MCon (MTArray x2' t2') mem loc2 | MTValue Types \<Rightarrow> False)) \<and>
             ((\<exists>p. accessStore stl2 mem = Some (MPointer p)) \<or> accessStore stl2 mem = None)" 
        using MTArray MCon.simps(2)[of x2 "MTArray x2' t2'" mem stl2] by simp
      obtain i1 l1 where i1def:"i1<x1 \<and>  accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) mem = Some (MPointer l1) \<and> (l1 = stl2 \<or> TypedMemSubPrefPtrs mem x1' t1' l1 stl2)" 
        using a20 by blast
      obtain i2 l2 where i2def:"i2<x2 \<and> accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) mem = Some (MPointer l2) \<and> (l2 = stl1 \<or> TypedMemSubPrefPtrs mem x2' t2' l2 stl1)" 
        using a10 by blast
      show False
      proof(cases "l1 = stl2")
        case t1:True
        then show ?thesis 
        proof(cases "l2 = stl1")
          case t2:True
          then have "MCon (MTArray x1' t1') mem stl2" using t1 i2def i1def a30 by fastforce
          have b1:"MCon (MTArray x2' t2') mem stl1" using t1 t2 i2def i1def a40 by fastforce
          have b2:"MCon (MTArray x1 (MTArray x1' t1')) mem stl1" using MTArray by simp


          show ?thesis using b1 MTArray.prems(3,4,5) 
            by (metis MConSubTypes \<open>MCon (MTArray x1' t1') mem stl2\<close> CompMemJustType.simps(2))
        next
          case False
          then have "TypedMemSubPrefPtrs mem x2' t2' l2 stl1" using i2def by simp
          moreover have "TypedMemSubPrefPtrs mem x1 (MTArray x1' t1') stl1 l2" using MTArray.prems(2) i2def 
            using MTArray.prems(4,5,6) TypedMemSubPrefPtrs.simps(2) TypedMemSubPrefPtrs_trns by blast
          moreover have "CompMemJustType (MTArray x1 (MTArray x1' t1')) (MTArray x2' t2')" using MTArray 
            by (metis CompMemTypes_asc CompMemJustType.simps(2))
          moreover have "MCon (MTArray x1 (MTArray x1' t1')) mem stl1" using MTArray.prems by auto
          moreover have "MCon (MTArray x2' t2') mem l2" using i2def a40 by fastforce
          moreover have "CompMemType mem x1 (MTArray x1' t1') (MTArray x2' t2') stl1 l2" 
            by (meson MTArray.prems(6) compMemTypes_trns i2def CompMemType.simps(2))
          ultimately show ?thesis using MTArray(2)[of l2 x2'] by blast
        qed
      next
        case False
        then show ?thesis 
        proof(cases "l2 = stl1")
          case t2:True
          have "TypedMemSubPrefPtrs mem x1' t1' l1 stl2" using False 
            using i1def by auto
          then show ?thesis using t2 
            by (metis CompMemType.simps(2) MConPtrsMustBeSubLocs2 MCon_imps_sub_Mcon MTArray.prems(4,5,6) compMemTypes_trns i2def)
        next
          case f2:False
          then have "TypedMemSubPrefPtrs mem x1' t1' l1 stl2" using i1def False by simp
          moreover have "TypedMemSubPrefPtrs mem x2' t2' l2 stl1" using i2def f2 by simp
          moreover have "CompMemJustType (MTArray x1' t1') (MTArray x2 (MTArray x2' t2'))" using MTArray 
            by (metis CompMemType_imps_CompMemJustType CompMemJustType.simps(2) CompMemType.simps(2))
          moreover have "MCon (MTArray x1' t1') mem l1" 
            using a30 i1def by fastforce
          moreover have "CompMemType mem x1' t1' (MTArray x2 (MTArray x2' t2')) l1 stl2" 
            by (meson CompMemType_asc_withSharedTarget CompTypeRemainsMCon MTArray.prems(4) MTArray.prems(6) calculation(1) i1def CompMemType.simps(2))
          ultimately have "\<not> TypedMemSubPrefPtrs mem x2 (MTArray x2' t2') stl2 l1"
            using MTArray(1)[of x1' l1] * False
            using MConSubTypes MTArray.prems(4) CompMemJustType.simps(2) MTArray(6) 
            by (metis BothMConImpsNotCompMemType CompMemType_asc_withSharedTarget compMemTypes_trns i1def CompMemType.simps(2))
          then show ?thesis using * False f2 
            using MConSubTypes MTArray.prems(4)  CompMemJustType.simps(2) 
            by (meson CompMemType_imps_CompMemJustType CompMemType_imps_TypedMemSubPrefPtrs CompTypeRemainsMCon MTArray.prems(1) MTArray.prems(6) compMemTypes_trns i2def CompMemType.simps(2))
        qed
      qed
    qed

  next
    case (MTValue x)
    then show ?case by fastforce
  qed
next
  case (MTValue x)
  then show ?case 
  proof(induction t1 arbitrary:x1 stl1)
    case (MTArray x1 t1)
    then show ?case 
      by fastforce
  next
    case (MTValue x)
    then show ?case by fastforce
  qed

qed

lemma TypedMemSubPrefPtrs_imps_notsame:
  assumes "TypedMemSubPrefPtrs m len'' arr'' stl1 prnt"
    and "MCon (MTArray len'' arr'') m stl1"
  shows "stl1 \<noteq> prnt" using assms
proof(induction arr'' arbitrary:len'' stl1)
  case (MTArray x1 arr'')
  obtain i l where iDef:"i<len'' \<and> accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some (MPointer l) \<and> (l = prnt \<or> TypedMemSubPrefPtrs m x1 arr'' l prnt)" 
    using MTArray.prems(1) unfolding TypedMemSubPrefPtrs.simps by blast
  then have mc:"MCon (MTArray x1 arr'') m l" using MTArray.prems(2) 
    using MCon_imps_sub_Mcon by blast
  then show ?case 
  proof(cases "l= prnt")
    case True
    then show ?thesis using iDef mc 
      using MConPtrsMustBeSubLocs MTArray.prems(2) by blast
  next
    case False
    then show ?thesis using MTArray.IH iDef mc 
      by (smt (verit, best) CompMemType_imps_CompMemJustType CompMemType_imps_TypedMemSubPrefPtrs MTArray.prems(2) TypedMemSubPrefOneWay CompMemType.simps(2))
  qed
next
  case (MTValue x)
  then show ?case by force
qed

lemma existingLocation_imps_allLocs:
  assumes "CompMemType m len (MTArray len' arr') subT prnt stl1"
    and "MCon (MTArray len (MTArray len' arr')) m prnt"
  shows "\<forall>i<len. \<forall>l. accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some (MPointer l) \<and> l\<noteq>stl1 \<and> TypedMemSubPrefPtrs m len' arr' l stl1
\<longrightarrow> CompMemType m len' arr' subT l stl1"
proof intros
  fix i l 
  assume asm1:"i < len"
    and asm2:"accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some (MPointer l) \<and> l \<noteq> stl1 \<and> TypedMemSubPrefPtrs m len' arr' l stl1"
  show "CompMemType m len' arr' subT l stl1" using assms asm2 asm1
  proof(induction arr' arbitrary:len' l)
    case (MTArray x1 arr')
    then show ?case 
      by (meson CompMemType_asc_withSharedTarget CompTypeRemainsMCon CompMemType.simps(2))
  next
    case (MTValue x)
    then show ?case 
      by (meson CompMemType_asc_withSharedTarget CompTypeRemainsMCon CompMemType.simps(2))
  qed
qed


lemma existingLocation_imps_allLocs_same:
  assumes "CompMemType m len t subT prnt stl1"
    and "MCon (MTArray len t) m prnt"
  shows "\<forall>i<len. \<forall>l. accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some (MPointer l) \<and> l =stl1 
\<longrightarrow> subT = t"
proof intros
  fix i l 
  assume asm1:"i < len"
    and asm2:"accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some (MPointer l) \<and> l = stl1 "
  show "subT = t" using assms asm2 asm1
  proof(induction t arbitrary:len l)
    case (MTArray x1 arr')

    obtain i'' ptr where ptrDef:"(i''<len \<and> accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) m = Some (MPointer ptr) 
                                  \<and> (ptr = stl1 \<and> MTArray x1 arr' = subT 
                                      \<or> CompMemType m x1 arr' subT ptr stl1))"  
      using MTArray.prems(1) unfolding CompMemType.simps(2) by blast
    then show ?case 
    proof(cases "ptr = l")
      case True
      then show ?thesis 
        using BothMConImpsNotCompMemType CompTypeRemainsMCon MCon_imps_sub_Mcon MTArray.prems(2,3) ptrDef by blast
    next
      case False
      then have "CompMemType m x1 arr' subT ptr stl1" using ptrDef 
        by (simp add: MTArray.prems(3))
      then show ?thesis using ptrDef False  
        using CompMemTypeSameLocsSameType MTArray.prems(2,3,4) CompMemType.simps(2) by blast
    qed

  next
    case (MTValue x)
    then show ?case by simp
  qed
qed

lemma CompMemForTopLocs:
  assumes "CompMemType (memory st) x11' x12' dt stl2 dloc1"
    and "\<not> LSubPrefL2 dloc1 (ShowL\<^sub>n\<^sub>a\<^sub>t(toploc (memory st)))"
    and "TypedMemSubPrefPtrs (memory st') x11' x12' stl2 dloc1"
    and "MCon (MTArray x11' x12') (memory st) stl2"
    and "\<not> LSubPrefL2 stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t(toploc (memory st)))"
    and "TypedMemSubPrefPtrs (memory st) x11' x12' stl2 dloc1"
    and "\<exists>ptr. accessStore l (memory st') = Some (MPointer ptr) \<and> LSubPrefL2 ptr (ShowL\<^sub>n\<^sub>a\<^sub>t(toploc (memory st))) \<and> MCon (MTArray x t) (memory st') ptr "
    and "\<forall>locs. locs \<noteq> l \<and> \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t(toploc (memory st))) \<longrightarrow> accessStore locs (memory st) = accessStore locs (memory st')"
    and "\<forall>locs tp x t. \<not>LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t(toploc (memory st))) \<longrightarrow> \<not>CompMemType (memory (st')) x t tp (ShowL\<^sub>n\<^sub>a\<^sub>t(toploc (memory st))) locs 
                                                                    \<and> \<not>TypedMemSubPrefPtrs (memory (st')) x t (ShowL\<^sub>n\<^sub>a\<^sub>t(toploc (memory st))) locs"
    and "accessStore l (memory st') = Some (MPointer (ShowL\<^sub>n\<^sub>a\<^sub>t(toploc (memory st))))"
    and "\<forall>dloc1 x11 x12 stl1 i. \<not> LSubPrefL2 dloc1 (ShowL\<^sub>n\<^sub>a\<^sub>t(toploc (memory st))) \<and> TypedMemSubPrefPtrs (memory st') x11 x12 stl1 dloc1 
                            \<longrightarrow> TypedMemSubPrefPtrs (memory st) x11 x12 stl1 dloc1"
    and "\<forall>l1 l2. LSubPrefL2 l1 (ShowL\<^sub>n\<^sub>a\<^sub>t(toploc (memory st)))
                        \<and> accessStore l1 (memory st') = Some (MPointer l2) \<longrightarrow> l2 = l1 \<and> l1 \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t(toploc (memory st)))"
  shows "CompMemType (memory st') x11' x12' dt stl2 dloc1" using assms(1,2,3,4,5,6)
proof(induction x12' arbitrary:x11' stl2)
  case (MTArray x1 x12')
  obtain i'' ptr where 
    ptrDef:"i''<x11' \<and> accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (memory st') = Some (MPointer ptr) 
     \<and> (ptr = dloc1 \<or> TypedMemSubPrefPtrs (memory st') x1 x12' ptr dloc1)" 
    using MTArray.prems unfolding TypedMemSubPrefPtrs.simps by blast
  then show ?case 
  proof(cases "ptr = dloc1")
    case True
    then have "(hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) \<noteq> l" using MTArray.prems 
      using assms(7)  ptrDef by force
    then have "accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (memory st') = accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (memory st)" 
      using MTArray.prems(5) assms(8)
      by (metis MemLSubPrefL2_specific_imps_general  )
    then show ?thesis using MTArray.prems ptrDef 
      by (metis True existingLocation_imps_allLocs_same CompMemType.simps(2))
  next
    case False
    then have "(hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) \<noteq> l" using MTArray.prems
      using assms  ptrDef False   by auto
    then have sameAccess:"accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (memory st') = accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (memory st)" 
      using MTArray.prems assms
      by (metis MemLSubPrefL2_specific_imps_general )
    then have "TypedMemSubPrefPtrs (memory st) x1 x12' ptr dloc1" using ptrDef MTArray.prems False assms
      by (simp add: MTArray.prems(2) )
    moreover have "CompMemType (memory st) x1 x12' dt ptr dloc1" 
      using calculation ptrDef  False existingLocation_imps_allLocs[OF MTArray.prems(1,4) ]  sameAccess by auto
    moreover have "TypedMemSubPrefPtrs (memory st') x1 x12' ptr dloc1" using ptrDef False by simp
    moreover have "MCon (MTArray x1 x12') (memory st) ptr " using ptrDef MTArray.prems(4) 
      by (metis MCon_imps_sub_Mcon sameAccess)
    moreover have "\<not> LSubPrefL2 ptr (ShowL\<^sub>n\<^sub>a\<^sub>t(toploc (memory st)))" 
      using MTArray.prems(2) SubPtrs_top ptrDef assms(12) by blast
    ultimately have "CompMemType (memory st') x1 x12' dt ptr dloc1" using MTArray.IH[of x1 ptr] 
        MTArray.prems by simp
    then show ?thesis using ptrDef by auto
  qed
next
  case (MTValue x)
  then show ?case by auto
qed



lemma CompMemType_imps_in_GetAllMemoryLocations_ptr:
  assumes "MCon (MTArray len2 arr2) mem stl2"
    and "CompMemType mem len2 arr2 (MTArray len3 arr3) stl2 locs"
  shows "\<forall>i<len3. hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<in> GetAllMemoryLocations (MTArray len2 arr2) stl2 mem" using assms
proof (induction arr2 arbitrary: len2 stl2)
  case (MTArray x11 x12)
  have "(\<exists>i<len2.
        \<exists>l. accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l) 
        \<and> (l = locs \<and> MTArray x11 x12 = MTArray len3 arr3 \<or> CompMemType mem x11 x12 (MTArray len3 arr3) l locs))" 
    using MTArray.prems(2) CompMemType.simps(2)[of mem len2 x11 x12 "(MTArray len3 arr3)" stl2 locs] by blast
  then obtain i l where iDef:"i<len2 \<and> accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l) 
              \<and> (l = locs \<and> MTArray x11 x12 = MTArray len3 arr3 \<or> CompMemType mem x11 x12 (MTArray len3 arr3) l locs)" by blast
  then have mc:"MCon (MTArray x11 x12) mem l" using MTArray.prems(1) 
    using MCon_imps_sub_Mcon by blast
  then show ?case
  proof(cases "l = locs")
    case True
    then have st:"MTArray x11 x12 = MTArray len3 arr3" using iDef 
      using MTArray.prems(1,2) existingLocation_imps_allLocs_same by blast
    then have "\<forall>i''<len3. hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i'') \<in> {hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)} \<union> GetAllMemoryLocations (MTArray len3 arr3) l mem" 
      using GetAllMemoryLocations_Arry_Contains_Indexs[OF mc] by blast
    then show ?thesis using GetAllMemoryLocations.simps(2)[of len2 "MTArray len3 arr3" stl2 mem] st True iDef by force
  next
    case False
    then have "CompMemType mem x11 x12 (MTArray len3 arr3) l locs" using iDef by simp
    then have "\<forall>i<len3. hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<in> GetAllMemoryLocations (MTArray x11 x12) l mem"
      using MTArray.IH[OF mc] by blast
    then show ?thesis using GetAllMemoryLocations.simps(2)[of len2 "MTArray x11 x12" stl2 mem] iDef by force
  qed
next
  case (MTValue x2)
  then show ?case using MTValue by auto
qed



lemma GetAllMemLocs_subset:
  assumes "CompMemType mem llen aarr t pParentPtr p"
    and "MCon (MTArray llen aarr) mem pParentPtr"
  shows "GetAllMemoryLocations t p mem \<subseteq> GetAllMemoryLocations (MTArray llen aarr) pParentPtr mem"
  using assms
proof(induction aarr arbitrary:llen pParentPtr)
  case (MTArray x1 aarr)
  then obtain i l where iDef:"i<llen \<and>
       accessStore (hash pParentPtr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l) \<and>
           (l = p \<and> MTArray x1 aarr = t \<or> CompMemType mem x1 aarr t l p)" 
    unfolding CompMemType.simps by blast
  show ?case 
  proof
    fix x 
    assume in1:"x \<in> GetAllMemoryLocations t p mem"
    then show "x \<in> GetAllMemoryLocations (MTArray llen (MTArray x1 aarr)) pParentPtr mem"
    proof(cases "l = p")
      case True
      then have " MTArray x1 aarr = t" using iDef 
        using MTArray.prems(1,2) existingLocation_imps_allLocs_same by blast
      then have "x \<in> GetAllMemoryLocations (MTArray x1 aarr) l mem" using in1 True by simp
      then show ?thesis using GetAllMemoryLocations.simps(2)[of llen "MTArray x1 aarr" pParentPtr mem ] iDef 
        by fastforce
    next
      case False
      then have "CompMemType mem x1 aarr t l p" using iDef by blast
      then have "GetAllMemoryLocations t p mem \<subseteq> GetAllMemoryLocations (MTArray x1 aarr) l mem"
        using MTArray.IH[of x1 l] iDef MTArray.prems by fastforce
      then show ?thesis using GetAllMemoryLocations.simps(2)[of llen "MTArray x1 aarr" pParentPtr mem ] iDef 
                               MTArray.prems in1 by force
    qed
  qed
  

next
  case (MTValue x)
  then have *:"t = MTValue x \<and> (\<exists>i<llen. hash pParentPtr (ShowL\<^sub>n\<^sub>a\<^sub>t i) = p)" 
    unfolding CompMemType.simps by blast
  then obtain i where **:"i<llen \<and> hash pParentPtr (ShowL\<^sub>n\<^sub>a\<^sub>t i) = p" by blast
  then have "hash pParentPtr (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<in> GetAllMemoryLocations (MTArray llen (MTValue x)) pParentPtr mem" 
    using GetAllMemoryLocations_Arry_Contains_Indexs[OF MTValue(2)] by blast 
  moreover have "GetAllMemoryLocations (MTValue x) p mem = {p}"
    unfolding GetAllMemoryLocations.simps by blast

  ultimately show ?case  using ** by (metis "*" empty_subsetI insert_subset)
qed

lemma sharedLocationsParentsMustBeArray:
  assumes "MCon (MTArray x11' x12') m' stl2"
    and "MCon (MTArray x11 x12) m' stl1"
    and "TypedMemSubPrefPtrs m' x11' x12' stl2 dloc1"
    and "TypedMemSubPrefPtrs m' x11 x12 stl1 dloc1"
    and "\<not> TypedMemSubPrefPtrs m' x11' x12' stl2 stl1"
    and "\<not> TypedMemSubPrefPtrs m' x11 x12 stl1 stl2"
    and "stl1 \<noteq> stl2"
  shows "(\<nexists>a1 a2. x12 = MTValue a1 \<or> x12' = MTValue a2)" 
proof
  assume *:"\<exists>a1 a2. x12 = MTValue a1 \<or> x12' = MTValue a2"
  then show False using assms(1,2,3,4,5,6,7)
  proof(induction x12 arbitrary: x11 stl1)
    case (MTArray x1 x12)
    then show ?case 
    proof(induction x12')
      case mta:(MTArray x1 x12')
      then show ?case using MTArray * by blast
    next
      case (MTValue x)
      then have a1:" (\<exists>i<x11'. hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i) = dloc1)"  using TypedMemSubPrefPtrs.simps(1)[of m' x11' x stl1 dloc1] by auto
      have "(\<exists>i<x11. \<exists>l. accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MPointer l) \<and> (l = dloc1 \<or> TypedMemSubPrefPtrs m' x1 x12 l dloc1))" 
        using MTValue.prems TypedMemSubPrefPtrs.simps(2) by simp
      then obtain i l where idef:"i<x11 \<and> accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MPointer l) \<and> (l = dloc1 \<or> TypedMemSubPrefPtrs m' x1 x12 l dloc1)" by blast
      have mcon1:"\<forall>i<x11'.
             (case accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' of None \<Rightarrow> False 
              | Some (MValue val) \<Rightarrow> (case MTValue x of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTValue x) m' (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
              | Some (MPointer loc2) \<Rightarrow> (case MTValue x of MTArray len' arr' \<Rightarrow> MCon (MTValue x) m' loc2 | MTValue Types \<Rightarrow> False)) \<and>
             ((\<exists>p. accessStore stl2 m' = Some (MPointer p)) \<or> accessStore stl2 m' = None)" 
        using MTValue.prems MCon.simps(2)[of x11' "MTValue x" m' stl2 ] by auto
      then have a2: "MCon (MTValue x) m' dloc1" using a1 
        using CompTypeRemainsMCon MTValue.prems CompMemType.simps(1) by blast
      have mcon2:"\<forall>i<x11.
             (case accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' of None \<Rightarrow> False 
              | Some (MValue val) \<Rightarrow> (case MTArray x1 x12 of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTArray x1 x12) m' (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
              | Some (MPointer loc2) \<Rightarrow> (case MTArray x1 x12 of MTArray len' arr' \<Rightarrow> MCon (MTArray x1 x12) m' loc2 | MTValue Types \<Rightarrow> False)) \<and>
             ((\<exists>p. accessStore stl1 m' = Some (MPointer p)) \<or> accessStore stl1 m' = None)"
        using MTValue.prems MCon.simps(2)[of x11 "MTArray x1 x12" m' stl1] by auto
      then show ?case 
      proof(cases "l = dloc1")
        case True
        then have "MCon (MTArray x1 x12) m' dloc1" using idef mcon2 by fastforce
        then show ?thesis using a2  
          by (metis MCon_sub_MTVal_imps_val MTValue.prems(3) Memoryvalue.distinct(1) 
              a1 option.distinct(1) option.inject MCon.simps(2))
      next
        case False
        then have a3:"MCon (MTArray x1 x12) m' l" using idef mcon2 by fastforce
        then have "TypedMemSubPrefPtrs m' x1 x12 l dloc1" using idef False by simp
        moreover have "\<not> TypedMemSubPrefPtrs m' x1 x12 l stl2" using MTValue.prems 
          using idef TypedMemSubPrefPtrs.simps(2) by blast 
        moreover have "\<not> TypedMemSubPrefPtrs m' x11' (MTValue x) stl2 l" 
        proof
          assume c1:"TypedMemSubPrefPtrs m' x11' (MTValue x) stl2 l"
          then have "(\<exists>i<x11'. hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i) = l)" using TypedMemSubPrefPtrs.simps(1)[of m' x11' x stl2 l] by blast
          then show False using c1 MTArray idef a3 a2 calculation(1) 
            by (metis MTypes.distinct(1) Memoryvalue.distinct(1) mcon_accessStore option.discI option.inject MCon.simps(2))
        qed
        moreover have "stl2 \<noteq> l" 
          using MTValue.prems idef TypedMemSubPrefPtrs.simps(2) by blast
        ultimately show ?thesis using MTValue(1)[of x1 l] using a3 mcon2 MTValue.prems(1,3,5) by blast
      qed
    qed
  next
    case (MTValue x)
    then show ?case 
    proof(induction x12' arbitrary: x11' stl2)
      case (MTArray x1 x12')
      then have a1:" (\<exists>i<x11. hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i) = dloc1)"  using TypedMemSubPrefPtrs.simps(1)[of m' x11' x stl1 dloc1] by auto
      have "(\<exists>i<x11'. \<exists>l. accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MPointer l) \<and> (l = dloc1 \<or> TypedMemSubPrefPtrs m' x1 x12' l dloc1))" 
        using MTArray.prems(4) TypedMemSubPrefPtrs.simps(2)[of m' x11' x1 x12' stl2 dloc1] by simp
      then obtain i l where idef:"i<x11' \<and> accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MPointer l) \<and> (l = dloc1 \<or> TypedMemSubPrefPtrs m' x1 x12' l dloc1)" by blast
      have mcon1:" \<forall>i<x11.
             (case accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' of None \<Rightarrow> False 
              | Some (MValue val) \<Rightarrow> (case MTValue x of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTValue x) m' (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
              | Some (MPointer loc2) \<Rightarrow> (case MTValue x of MTArray len' arr' \<Rightarrow> MCon (MTValue x) m' loc2 | MTValue Types \<Rightarrow> False)) \<and>
             ((\<exists>p. accessStore stl1 m' = Some (MPointer p)) \<or> accessStore stl1 m' = None)" 
        using MTArray.prems(3) MCon.simps(2)[of x11 "MTValue x" m' stl1 ] by auto
      then have a2: "MCon (MTValue x) m' dloc1" using a1 
        using CompTypeRemainsMCon MTValue.prems(3) CompMemType.simps(1) by blast
      have mcon2:"\<forall>i<x11'.
             (case accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' of None \<Rightarrow> False 
              | Some (MValue val) \<Rightarrow> (case MTArray x1 x12' of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTArray x1 x12') m' (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
              | Some (MPointer loc2) \<Rightarrow> (case MTArray x1 x12' of MTArray len' arr' \<Rightarrow> MCon (MTArray x1 x12') m' loc2 | MTValue Types \<Rightarrow> False)) \<and>
             ((\<exists>p. accessStore stl2 m' = Some (MPointer p)) \<or> accessStore stl2 m' = None)"
        using MTArray.prems(2) MCon.simps(2)[of x11' "MTArray x1 x12'" m' stl2] by auto
      then show ?case 
      proof(cases "l = dloc1")
        case True
        then have "MCon (MTArray x1 x12') m' dloc1" using idef mcon2 by fastforce
        then show ?thesis using a2  
          by (metis MCon_sub_MTVal_imps_val MTValue.prems(3) Memoryvalue.distinct(1) a1  option.distinct(1) option.inject MCon.simps(2))
      next
        case False
        then have a3:"MCon (MTArray x1 x12') m' l" using idef mcon2 by fastforce
        then have "TypedMemSubPrefPtrs m' x1 x12' l dloc1" using idef False by simp
        moreover have "\<not> TypedMemSubPrefPtrs m' x1 x12' l stl1" using MTArray.prems(6) 
          using idef TypedMemSubPrefPtrs.simps(2) by blast 
        moreover have "\<not> TypedMemSubPrefPtrs m' x11 (MTValue x) stl1 l" 
        proof
          assume c1:"TypedMemSubPrefPtrs m' x11 (MTValue x) stl1 l"
          then have "(\<exists>i<x11. hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i) = l)" using TypedMemSubPrefPtrs.simps(1)[of m' x11 x stl1 l] by blast
          then show False using c1 MTArray idef a3 a2 calculation(1) 
            by (metis MTypes.distinct(1) Memoryvalue.distinct(1) mcon_accessStore option.discI option.inject MCon.simps(2))
        qed
        moreover have "stl1 \<noteq> l" 
          using MTArray.prems(6) idef TypedMemSubPrefPtrs.simps(2) by blast
        ultimately show ?thesis using MTArray.IH[of x1 l] using a3 mcon2 MTArray.prems(1,3,5) by blast
      qed
    next
      case (MTValue x')
      then have " (\<exists>i<x11'. hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i) = dloc1)"  using TypedMemSubPrefPtrs.simps(1)[of m' x11' x' stl2 dloc1] by auto
      moreover have " (\<exists>i<x11. hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i) = dloc1)" using MTValue by auto
      ultimately have "stl1 = stl2" using hash_injective ShowLNatDot by blast
      then show ?case using MTValue(8) by simp
    qed
  qed
qed

lemma sharedParentSharedSubLocTypes:
  assumes "TypedMemSubPrefPtrs m' x11 x12 stl1 dloc1"
    and "TypedMemSubPrefPtrs m' x11' x12' stl2 dloc1"
    and "p'' \<noteq> stl1 \<and> tp''' = MTArray tp'''L tp'''T \<and> CompMemType m' tp'''L tp'''T (MTArray x11 x12) p'' stl1"
    and "CompMemType m' tp'''L tp'''T (MTArray x11' x12') p'' stl2"
    and "MCon tp''' m' p''"
  shows "\<exists>dt. CompMemType m' x11' x12' dt stl2 dloc1 \<and> CompMemType m' x11 x12 dt stl1 dloc1" using assms(1,2,3,4,5)
proof(induction x12' arbitrary:x11' stl2)
  case (MTArray x1' x12')
  then show ?case 
  proof(induction x12 arbitrary:x11 stl1)
    case (MTArray x1 x12)
    have "(\<exists>i<x11'. \<exists>l. accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MPointer l) \<and> (l = dloc1 \<or> TypedMemSubPrefPtrs m' x1' x12' l dloc1))" 
      using TypedMemSubPrefPtrs.simps(2)[of m' x11' x1' x12' stl2 dloc1] MTArray.prems by simp
    then obtain i l where idef:"i<x11' \<and> accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MPointer l) \<and> (l = dloc1 \<or> TypedMemSubPrefPtrs m' x1' x12' l dloc1)" by blast
    have "(\<exists>i<x11. \<exists>l. accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MPointer l) \<and> (l = dloc1 \<or> TypedMemSubPrefPtrs m' x1 x12 l dloc1))" 
      using TypedMemSubPrefPtrs.simps(2)[of m' x11 x1 x12 stl1 dloc1] MTArray.prems by simp
    then obtain i' l' where i'def:"i'<x11 \<and> accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i')) m' = Some (MPointer l') \<and> (l' = dloc1 \<or> TypedMemSubPrefPtrs m' x1 x12 l' dloc1)" by blast
    then show ?case 
    proof(cases "l = dloc1")
      case t6:True
      then have g1:"CompMemType m' x11' (MTArray x1' x12') (MTArray x1' x12') stl2 dloc1" using idef by auto
      then show ?thesis 
      proof(cases "l' = dloc1")
        case t7:True
        then have g2:"CompMemType m' x11 (MTArray x1 x12) (MTArray x1 x12) stl1 dloc1" using i'def by auto
        have "CompMemType m' tp'''L tp'''T (MTArray x1' x12') p'' dloc1" 
          using MTArray.prems g1 g2 compMemTypes_trns  by blast
        moreover have "CompMemType m' tp'''L tp'''T (MTArray x1 x12) p'' dloc1" 
          using MTArray.prems g1 g2 compMemTypes_trns[of m' x11 "(MTArray x1 x12)" "(MTArray x1 x12)" stl1 dloc1 tp'''L tp'''T p'']  by simp
        ultimately have g3:"(MTArray x1' x12')  = (MTArray x1 x12)" 
          using CompMemTypeSameLocsSameType MTArray.prems   by blast
        then show ?thesis using g1 g2  by blast
      next
        case False
        then have g2:"TypedMemSubPrefPtrs m' x1 x12 l' dloc1" using i'def by simp
        then have "CompMemType m' tp'''L tp'''T (MTArray x1' x12') p'' dloc1" using g1 MTArray.prems  compMemTypes_trns by blast
        then have g4:"CompMemType m' x11 (MTArray x1 x12) (MTArray x1' x12') stl1 dloc1" using g2 g1 MTArray.prems
          by (metis CompMemType_asc_withSharedTarget CompTypeRemainsMCon MTArray.prems(2,4) assms(3))
        then show ?thesis using g1 g2 i'def False g4  by blast
      qed
    next
      case False
      then have g1:"TypedMemSubPrefPtrs m' x1' x12' l dloc1" using idef by simp
      then show ?thesis 
      proof(cases "l' = dloc1")
        case t7:True
        then have g2:"CompMemType m' x11 (MTArray x1 x12) (MTArray x1 x12) stl1 dloc1" using i'def by auto
        then have "CompMemType m' tp'''L tp'''T (MTArray x1 x12) p'' dloc1" using g1 MTArray.prems compMemTypes_trns by blast
        then have g4:"CompMemType m' x11' (MTArray x1' x12') (MTArray x1 x12) stl2 dloc1" using g2 g1 MTArray.prems 
          by (metis CompMemType_asc_withSharedTarget CompTypeRemainsMCon MTArray.prems(3) assms(3))
        then show ?thesis using g1 g2 by blast
      next
        case f7:False
        then have g2:"TypedMemSubPrefPtrs m' x1 x12 l' dloc1" using i'def by simp
        have "TypedMemSubPrefPtrs m' x1' x12' l dloc1" using g1 by simp
        moreover have "TypedMemSubPrefPtrs m' x11 (MTArray x1 x12) stl1 dloc1" 
          using MTArray.prems by auto


        moreover have " p'' \<noteq> l \<and> tp''' = MTArray tp'''L tp'''T \<and> CompMemType m' tp'''L tp'''T (MTArray x1' x12') p'' l" 
          using idef BothMConImpsNotCompMemType CompTypeRemainsMCon MTArray.prems  compMemTypes_trns CompMemType.simps(2) assms
          by metis
        moreover have "tp''' = MTArray tp'''L tp'''T \<and> CompMemType m' tp'''L tp'''T (MTArray x11 (MTArray x1 x12)) p'' stl1" 
          by (simp add: MTArray.prems)
        moreover have "MCon (MTArray x1' x12') m' l" 
          using CompTypeRemainsMCon calculation assms by blast
        moreover have "MCon (MTArray x11 (MTArray x1 x12)) m' stl1" 
          using MTArray.prems
          using CompTypeRemainsMCon by blast
        moreover have "p'' \<noteq> stl1" 
          by (simp add: MTArray.prems)
        ultimately have " \<exists>dt. CompMemType m' x1' x12' dt l dloc1 \<and> CompMemType m' x11 (MTArray x1 x12) dt stl1 dloc1" using MTArray(2)
          using assms by presburger
        then show ?thesis   
          using CompMemTypeSameLocsSameType compMemTypes_trns assms CompMemType_asc_withSharedTarget CompTypeRemainsMCon 
          by (metis MTArray.prems(3,4,5) )
      qed
    qed

  next
    case (MTValue x)
    then show ?case by (metis CompMemType_asc_withSharedTarget CompTypeRemainsMCon MTValue.prems(2) 
          TypedMemSubPrefPtrs.simps(1) compMemTypes_trns CompMemType.simps(1) assms(3))
  qed
next
  case (MTValue x)
  then show ?case using assms 
    by (metis CompMemType_asc_withSharedTarget CompTypeRemainsMCon MTValue.prems TypedMemSubPrefPtrs.simps(1) compMemTypes_trns CompMemType.simps(1))
qed

lemma CompMem_SameLocs_SameSubT:
  assumes "CompMemType m len subT t l'' p''"
    and "MCon (MTArray len subT) m l''"
    and "CompMemType m len subT newt l'' p''"
  shows "newt = t" using assms
proof(induction subT arbitrary: l'' len)
  case (MTArray x1 subT)
  then show ?case 
    using CompTypeRemainsMCon 
    using CompMemTypeSameLocsSameType by blast
next
  case (MTValue x)
  then show ?case by simp
qed



lemma typedPrefix_imp_SubPref:
  shows "TypedMemSubPref child parent t \<longrightarrow> LSubPrefL2 child parent"
proof(induction t arbitrary:parent)
  case (MTArray x1 t)
  show ?case 
  proof intros
    assume *:"TypedMemSubPref child parent (MTArray x1 t)"
    then have **:"(\<exists>i<x1. TypedMemSubPref child (hash parent (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t \<or> child = (hash parent (ShowL\<^sub>n\<^sub>a\<^sub>t i)))" 
      using TypedMemSubPref.simps(2)[of child parent x1 t] by auto
    then show "LSubPrefL2 child parent" 
    proof(cases "\<exists>i<x1. child = (hash parent (ShowL\<^sub>n\<^sub>a\<^sub>t i))")
      case True
      then show ?thesis unfolding LSubPrefL2_def by auto
    next
      case False
      then obtain i where "i < x1 \<and> TypedMemSubPref child (hash parent (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t" using ** by auto
      then have "LSubPrefL2 child (hash parent (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using MTArray by auto

      then show "LSubPrefL2 child parent" unfolding LSubPrefL2_def 
        using LSubPrefL2_def Not_Sub_More_Specific by blast
    qed

  qed
next
  case (MTValue x)
  then show ?case 
  proof intros
    assume "TypedMemSubPref child parent (MTValue x)"
    then show "LSubPrefL2 child parent" unfolding LSubPrefL2_def by auto
  qed
qed


lemma writtenMem_between_same_empty:
  shows "WrittenMem_between st st = {}" unfolding WrittenMem_between_def by auto

abbreviation mymemory22::MemoryT
  where "mymemory22 \<equiv>
    \<lparr>mapping = fmap_of_list
      [(STR ''1.1.0'', MValue STR ''False''),
       (STR ''0.1.0'', MValue STR ''True''),
       (STR ''1.0'', MPointer STR ''2.0''),
       (STR ''1.0.0'', MValue STR ''False''),
       (STR ''0.2.0'', MValue STR ''True''),
       (STR ''0.0'', MPointer STR ''0.0'')],
     toploc = 1\<rparr>"
value "GetAllMemoryLocations (MTArray 3 (MTArray 2 (MTValue TBool))) STR ''0'' mymemory22"



end