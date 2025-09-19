section\<open>Defining the properties of type consistency for the memory datatypes Isabelle Hol\<close>
theory TypeSafe_Storage
  imports TypeSafe_Base_Types 
begin


(*Helper function for simplified handling of SType recursion, i.e. proving non-possible branches*)
fun stype_size :: "STypes \<Rightarrow> nat" where
  "stype_size (STValue _) = 1"
| "stype_size (STArray _ S) = 1 + stype_size S"
| "stype_size (STMap _ S) = 1 + stype_size S"

lemma stype_size_positive: "stype_size t > 0"
  by (induction t rule: STypes.induct) simp_all

lemma stype_size_strict_decrease_array: "stype_size arr < stype_size (STArray len arr)"
  by (simp)

lemma stype_size_strict_decrease_map: "stype_size toTyp < stype_size (STMap fromTyp toTyp)"
  by (simp)

primrec TypedStoSubPref:: "Location \<Rightarrow> Location \<Rightarrow> STypes \<Rightarrow> bool"
  where 
    "TypedStoSubPref child parent (STValue t) = (child = parent)"
  | "TypedStoSubPref child parent (STArray len t) = (\<exists>i<len. TypedStoSubPref child (hash parent (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t \<or> child = (hash parent (ShowL\<^sub>n\<^sub>a\<^sub>t i)))"
  | "TypedStoSubPref child parent (STMap k v) = False"


lemma stoTypedPrefix_imp_SubPref:
  shows "TypedStoSubPref child parent t \<longrightarrow> LSubPrefL2 child parent"
proof(induction t arbitrary:parent)
  case (STArray x1 t)
  show ?case 
  proof intros
    assume *:"TypedStoSubPref child parent (STArray x1 t)"
    then have **:"(\<exists>i<x1. TypedStoSubPref child (hash parent (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t \<or> child = (hash parent (ShowL\<^sub>n\<^sub>a\<^sub>t i)))" 
      using TypedStoSubPref.simps(2)[of child parent x1 t] by auto
    then show "LSubPrefL2 child parent" 
    proof(cases "\<exists>i<x1. child = (hash parent (ShowL\<^sub>n\<^sub>a\<^sub>t i))")
      case True
      then show ?thesis unfolding LSubPrefL2_def by auto
    next
      case False
      then obtain i where "i < x1 \<and> TypedStoSubPref child (hash parent (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t" using ** by auto
      then have "LSubPrefL2 child (hash parent (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using STArray by auto

      then show "LSubPrefL2 child parent" unfolding LSubPrefL2_def 
        using LSubPrefL2_def Not_Sub_More_Specific by blast
    qed

  qed
next
  case (STValue x)
  then show ?case 
  proof intros
    assume "TypedStoSubPref child parent (STValue x)"
    then show "LSubPrefL2 child parent" unfolding LSubPrefL2_def by auto
  qed
next 
  case (STMap k v) 
  then show ?case by simp
qed

lemma neg_MemLSubPrefL2_imps_TypedStoSubPref:
  assumes "\<not> LSubPrefL2 child prnt"
  shows "\<not>TypedStoSubPref child prnt t" using assms  using stoTypedPrefix_imp_SubPref by blast


lemma stoMoreSpecificTypedSubPref:
  assumes "( \<forall>l l'. TypedStoSubPref l destl (STArray x t) \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l)"
  shows "\<forall>i<x. ( \<forall>l l'. TypedStoSubPref l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l)" using assms(1)
proof (induction t arbitrary:x)
  case (STArray x1 t)
  show ?case 
  proof intros
    fix i l l'
    assume *:"i<x"
      and **:"TypedStoSubPref l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (STArray x1 t) \<and> accessStore l v' = Some (MPointer l')"
    have b10:"TypedStoSubPref l destl (STArray x (STArray x1 t)) \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l" using STArray by metis
    then show "l' =l" using  STArray(1) b10 * **
      by (meson TypedStoSubPref.simps(2))
  qed
next
  case (STValue x)
  then show ?case by auto
next 
  case (STMap k v)
  then show ?case 
    by (meson TypedStoSubPref.simps(3))
qed

subsection \<open>Storage type conformity\<close>

text \<open>The SCon function works similarly to the MCon function and searches a given 
      storage starting at location (loc) to ensure all sub locations conform to their given types.
    There are two main differences to MCon. 1. The support for the STMap type.
    2. There is no need to look up pointer locations when indexing through arrays, storage does not 
  support pointers in solidity and so a direct lookup can be performed.\<close>
primrec SCon :: "STypes \<Rightarrow> Location \<Rightarrow> StorageT \<Rightarrow>bool"
  where
    "SCon (STValue typ) loc fm= ((typeCon typ (accessStorage typ loc fm)))"
  |"SCon (STArray len arr) loc fm = (\<forall>i<len. SCon arr (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) fm)"
  |"SCon (STMap fromTyp toTyp) loc fm = (\<forall>i::String.literal. (typeCon fromTyp i)  \<longrightarrow> SCon toTyp (hash loc i) fm)"


lemma subSCon:
  assumes "SCon (STArray (Suc x) t') srcl srcMem"
  shows "SCon (STArray (x) t') srcl srcMem" using assms 
proof(induction t' arbitrary: x srcl)
  case (STArray x1 t')
  then show ?case by auto
next
  case (STMap x1 t')
  then show ?case by simp
next
  case (STValue x)
  then show ?case by simp
qed


primrec TypedStoSubpref :: "Location \<Rightarrow> Location \<Rightarrow> STypes \<Rightarrow> bool"
  where 
    "TypedStoSubpref child parent (STValue typ) = (child = parent)"
  | "TypedStoSubpref child parent (STArray len arr) = (child = parent \<or> 
                                                      (\<exists>i<len. TypedStoSubpref child (hash parent (ShowL\<^sub>n\<^sub>a\<^sub>t i)) arr))"
  | "TypedStoSubpref child parent (STMap fromTyp toTyp) = ((child = parent) 
                                \<or> (\<exists>i::String.literal. (typeCon fromTyp i) \<and> (TypedStoSubpref child (hash parent i) toTyp)))"



lemma TypedStoSubpref_b:
  assumes "TypedStoSubpref l1 l2 t"
  shows "(\<exists>a. hash l2 a = l1) \<or> l1 = l2" using assms
proof(induction t arbitrary:l2)
  case (STArray x1 t)
  then have a1:"(l1 = l2 \<or> (\<exists>i<x1. TypedStoSubpref l1 (hash l2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t))" using TypedStoSubpref.simps(2)[of l1 l2 x1 t] by simp
  then show ?case 
  proof(cases "l1 = l2")
    case True
    then show ?thesis by simp
  next
    case False
    then have "\<exists>i<x1. TypedStoSubpref l1 (hash l2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t" using a1 by simp
    then show ?thesis by (metis STArray.IH hash_suffixes_associative)
  qed
next
  case (STMap x1 t)
  then have a1:" (l1 = l2 \<or> (\<exists>i. typeCon x1 i \<and> TypedStoSubpref l1 (hash l2 i) t))" using TypedStoSubpref.simps(3)[of l1 l2 x1 t ] by auto
  then show ?case
  proof(cases "l1 = l2")
    case True
    then show ?thesis by auto
  next
    case False
    then have "(\<exists>i. typeCon x1 i \<and> TypedStoSubpref l1 (hash l2 i) t)" using a1 by auto
    then show ?thesis using STMap by (metis hash_suffixes_associative)
  qed

next
  case (STValue x)
  then show ?case by simp

qed



lemma TypedStoSubpref_hashes:
  shows "TypedStoSubpref l2' (hash loc kv) t \<longrightarrow> l2' \<noteq> loc" using TypedStoSubpref_b 
  by (metis hash_inequality hash_suffixes_associative)

lemma TypedStoSubpref_sameLoc:
  shows "TypedStoSubpref l1 l1 tp"
proof(cases tp)
  case (STArray x11 x12)
  then show ?thesis by simp
next
  case (STMap x21 x22)
  then show ?thesis by simp
next
  case (STValue x3)
  then show ?thesis by simp
qed

lemma typedStoSub_imps_negInv:
  assumes "short \<noteq> short'"
  shows "TypedStoSubpref short short' t' \<longrightarrow> \<not> TypedStoSubpref short' short t" 
proof
  assume *:"TypedStoSubpref short short' t'"
  show "\<not> TypedStoSubpref short' short t"
  proof
    assume **:"TypedStoSubpref short' short t"
    obtain a where  a10:"(hash short' a = short)" using * assms TypedStoSubpref_b by blast
    obtain a' where  a20:"(hash short a' = short')" using ** assms TypedStoSubpref_b by blast
    show False using a10 a20 
      by (metis "*" TypedStoSubpref_hashes)
  qed
qed

primrec subStoTp :: "STypes \<Rightarrow> STypes \<Rightarrow> bool"
  where 
    "subStoTp child (STValue typ) = (child = (STValue typ))"
  | "subStoTp child (STArray len arr) = (child = (STArray len arr) \<or> (subStoTp child arr))"
  | "subStoTp child (STMap fromTyp toTyp) = ((child = (STMap fromTyp toTyp)) \<or> (subStoTp child toTyp))"

primrec CompStoType :: "STypes  \<Rightarrow> STypes \<Rightarrow> Location \<Rightarrow> Location \<Rightarrow> bool"
  where 
    "CompStoType (STValue typ) childtp  parentloc childloc= (childtp = (STValue typ) \<and> (parentloc = childloc))"
  | "CompStoType (STArray len arr) childtp parentloc childloc = (((childtp = STArray len arr) \<and> parentloc = childloc) \<or>
                                                                (\<exists>i<len. CompStoType arr childtp (hash parentloc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) childloc))"
  | "CompStoType (STMap fromTyp toTyp) childtp parentloc childloc = ( (childtp = STMap fromTyp toTyp \<and> parentloc = childloc) \<or> (\<exists>i::String.literal. 
                                                                  (typeCon fromTyp i \<and>  (CompStoType toTyp childtp (hash parentloc i) childloc))))"

lemma CompStoType_imps_subStoTp:
  assumes "CompStoType t childtp  parentloc childloc"
  shows "subStoTp childtp t" using assms 
proof(induction t arbitrary:parentloc)
  case (STArray x1 t)
  then show ?case by auto
next
  case (STMap x1 t)
  then show ?case by auto
next
  case (STValue x)
  then show ?case by simp
qed

lemma CompStoType_imps_TypedStoSubpref:
  assumes "CompStoType t tp l'' l"
  shows "TypedStoSubpref l l'' t" using assms
proof(induction t arbitrary:l'')
  case (STArray x1 t)
  then show ?case by auto
next
  case (STMap x1 t)
  then show ?case by auto
next
  case (STValue x)
  then have "l'' = l" unfolding CompStoType.simps by simp
  then show ?case by simp
qed


lemma CompStoType_sameLocNdTyp:
  shows "CompStoType tp1 tp1 l1 l1"
proof(cases tp1)
  case (STArray x11 x12)
  then show ?thesis by simp
next
  case (STMap x21 x22)
  then show ?thesis by simp
next
  case (STValue x3)
  then show ?thesis by simp
qed

lemma CompStoType_imp_subType: 
  shows "loc \<noteq> loc' \<and>  CompStoType t1 t2 loc loc' \<longrightarrow> (\<exists>t. subStoTp t1 t \<and> t = t1)"
proof(induction t1)
  case (STArray x1 t1)
  then show ?case by simp
next
  case (STMap x1 t1)
  then show ?case by simp
next
  case (STValue x)
  then show ?case by simp
qed


lemma CompStoType_imps_subloc:
  shows "loc \<noteq> l2' \<and> CompStoType t1 t2 loc l2' \<longrightarrow> (\<exists>i. hash loc i = l2')"
proof(induction t1 arbitrary:loc)
  case (STArray x1 t1)
  show ?case 
  proof intros
    assume *:"loc \<noteq> l2' \<and> CompStoType (STArray x1 t1) t2 loc l2'"
    then have a1:"(\<exists>i<x1. CompStoType t1 t2 (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) l2')" 
      using CompStoType.simps(2)[of x1 t1 t2 loc l2'] by auto
    then show "(\<exists>i. hash loc i = l2')"  by (metis STArray hash_suffixes_associative)
  qed
next
  case (STMap x1 t1)
  show ?case 
  proof intros
    assume *:"loc \<noteq> l2' \<and> CompStoType (STMap x1 t1) t2 loc l2'"
    then have a1:"(\<exists>i. typeCon x1 i \<and> CompStoType t1 t2 (hash loc i) l2')" 
      using CompStoType.simps(3)[of x1 t1 t2 loc l2'] by auto
    then show " (\<exists>i. hash loc i = l2')" by (metis STMap hash_suffixes_associative)

  qed
next
  case (STValue x)
  then show ?case by auto
qed

lemma CompStoType_sameLoc_sameType:
  assumes "CompStoType t1 t2 l1 l1"
  shows "t1 = t2"
proof(cases t1)
  case (STArray x11 x12)
  then have "CompStoType (STArray x11 x12) t2 l1 l1" using STArray assms by auto
  then have "(t2 = STArray x11 x12 \<and> l1 = l1 \<or> (\<exists>i<x11. CompStoType x12 t2 (hash l1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) l1))" using CompStoType.simps(2)[of x11 x12 t2 l1 l1] by simp
  then show ?thesis  by (metis CompStoType_imps_subloc STArray hash_inequality hash_suffixes_associative)
next
  case (STMap x21 x22)
  then show ?thesis using assms by (metis CompStoType_imps_subloc hash_inequality hash_suffixes_associative CompStoType.simps(3))
next
  case (STValue x3)
  then show ?thesis using assms by simp
qed


lemma comp_stotype_size_le:
  "CompStoType t1 t2 l1 l2 \<Longrightarrow> stype_size t2 \<le> stype_size t1"
proof (induction t1 arbitrary: t2 l1 l2)
  case (STArray x1 t1)
  then show ?case by fastforce
next
  case (STMap x1 t1)
  then show ?case by fastforce
next
  case (STValue x)
  then show ?case by simp
qed


lemma comp_stotype_same_type_same_loc:
  shows "CompStoType t t l1 l2 \<Longrightarrow> l1 = l2"
proof (induction t arbitrary: l1 l2)
  case (STArray x1 t)
  then have a1:"STArray x1 t = STArray x1 t \<and> l1 = l2 \<or> (\<exists>i<x1. CompStoType t (STArray x1 t) (hash l1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) l2)" 
    unfolding CompStoType.simps by blast
  show "l1 = l2"
  proof (cases "l1 = l2")
    case True
    then show ?thesis by blast
  next
    case False
    then obtain i where idef: "i<x1 \<and> CompStoType t (STArray x1 t) (hash l1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) l2" 
      using a1 by blast
    then have "stype_size (STArray x1 t) \<le> stype_size t" 
      using comp_stotype_size_le by blast
    then have "stype_size (STArray x1 t) < stype_size (STArray x1 t)" by simp
    then show ?thesis by simp
  qed
next
  case (STMap x1 t)
  then have a1:"l1 = l2 \<or> (\<exists>i. typeCon x1 i \<and> CompStoType t (STMap x1 t) (hash l1 i) l2)" 
    unfolding CompStoType.simps by blast
  show "l1 = l2"
  proof (cases "l1 = l2")
    case True
    then show ?thesis by blast
  next
    case False
    then obtain i where idef: "typeCon x1 i \<and> CompStoType t (STMap x1 t) (hash l1 i) l2" 
      using a1 by blast
    then have "stype_size (STMap x1 t) \<le> stype_size t" 
      using comp_stotype_size_le by blast
    then have "stype_size (STMap x1 t) < stype_size (STMap x1 t)" by simp
    then show ?thesis by simp
  qed
next
  case (STValue x)
  then show ?case by simp
qed

definition compPointers :: "Stack \<Rightarrow> (String.literal, Type \<times> Denvalue) fmap \<Rightarrow> bool" where
  "compPointers st denval = (\<forall>tp1 tp2 l1 l2 l1' l2' stl1 stl2. 
    (Storage tp1, l1) |\<in>| fmran denval \<and> (Storage tp2, l2) |\<in>| fmran denval \<and>
    ((l1 = Stackloc l1' \<and> accessStore l1' st = Some(KStoptr stl1)) \<or> (l1 = Storeloc stl1)) \<and>
    ((l2 = Stackloc l2' \<and> accessStore l2' st = Some(KStoptr stl2)) \<or> (l2 = Storeloc stl2)) \<longrightarrow>
    (if TypedStoSubpref stl2 stl1 tp1 then CompStoType tp1 tp2 stl1 stl2 
     else if TypedStoSubpref stl1 stl2 tp2 then CompStoType tp2 tp1 stl2 stl1
     else True))"

lemma TypedStoSubpref_child_imps_prnt:
  assumes "TypedStoSubpref (hash x4 i) p' t"
    and "CHR ''.'' \<notin> set(String.explode i)"
    and "hash x4 i \<noteq> p'"
  shows "TypedStoSubpref x4 p' t"
  using assms
proof(induction t arbitrary:x4 i p')
  case (STArray x1 t)
  then show ?case using hash_injective typeConNoDots ShowLNatDot 
    by (metis TypedStoSubpref.simps(2))
next
  case (STMap x1 t)
  then have "(\<exists>i'. typeCon x1 i' \<and> TypedStoSubpref (hash x4 i) (hash p' i') t)" unfolding TypedStoSubpref.simps by simp
  then obtain i' where i'def:"typeCon x1 i' \<and> TypedStoSubpref (hash x4 i) (hash p' i') t" by blast
  then have noDot:"CHR ''.'' \<notin> set (literal.explode i')" using typeConNoDots[of x1 i'] i'def by blast
  then show ?case
  proof(cases "(hash x4 i)  = (hash p' i')")
    case True
    then show ?thesis using hash_injective STMap True noDot
      by (metis TypedStoSubpref.simps(3))
  next
    case False
    then have "x4 = p' \<or> (\<exists>i. typeCon x1 i \<and> TypedStoSubpref x4 (hash p' i) t)" using STMap.IH[of x4 i "(hash p' i')"] i'def noDot 
      using STMap.prems(2) by blast
    then show ?thesis by simp
  qed
next
  case (STValue x)
  then show ?case unfolding TypedStoSubpref.simps by blast
qed 

lemma TypedStoSubpref_specific_unreachanble_arry:
  assumes "destl \<noteq> srcl"
    and "\<not> TypedStoSubpref srcl destl (STArray x t')"
    and "i < x"
  shows "\<not> TypedStoSubpref (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t'"
proof

  assume *:"TypedStoSubpref (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t'"
  have **:"hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<noteq> hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i) " using assms 
    by (metis hash_never_equal_prefix)
  then have " TypedStoSubpref srcl (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t'" 
    using TypedStoSubpref_child_imps_prnt[OF * _ **] ShowLNatDot assms by auto
  then show False using assms by simp
qed

lemma TypedStoSubpref_specific_unreachanble_map:
  assumes "destl \<noteq> srcl"
    and "\<not> TypedStoSubpref srcl destl (STMap x t')"
    and "typeCon x i "
  shows "\<not> TypedStoSubpref (hash srcl i) (hash destl i) t'"
proof

  assume *:"TypedStoSubpref (hash srcl ( i)) (hash destl ( i)) t'"
  have **:"hash srcl ( i) \<noteq> hash destl ( i) " using assms 
    by (metis hash_never_equal_prefix)
  then have " TypedStoSubpref srcl (hash destl ( i)) t'" 
    using TypedStoSubpref_child_imps_prnt[OF * _ **] assms typeConNoDots by auto
  then show False using assms by simp
qed

lemma NotRelatedPrnt_imps_notRelatedChild:
  assumes "\<not> TypedStoSubpref x4 l''' t"
    and "\<not> TypedStoSubpref l''' x4 struct" 
    and "TypedStoSubpref l l''' t"
  shows "\<not> TypedStoSubpref l x4 struct " 
proof
  assume asm1:"TypedStoSubpref l x4 struct"
  show False using asm1 assms
  proof(induction struct arbitrary:x4)
    case (STArray x1 struct)
    have "l = x4 \<or> (\<exists>i<x1. TypedStoSubpref l (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) struct)" 
      using STArray.prems(1) unfolding TypedStoSubpref.simps by auto
    moreover have "l \<noteq> x4" using STArray.prems(2) assms(3) by auto
    ultimately obtain i where idef:"i<x1 \<and> TypedStoSubpref l (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) struct" by auto
    then have "CHR ''.'' \<notin> set (literal.explode (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using ShowLNatDot[of i] by blast
    then show ?case using idef 
      by (metis STArray.IH STArray.prems(2,3) TypedStoSubpref_child_imps_prnt TypedStoSubpref_sameLoc assms(3) TypedStoSubpref.simps(2))
  next
    case (STMap x1 struct)
    have "l = x4 \<or> (\<exists>i. typeCon x1 i \<and> TypedStoSubpref l (hash x4 i) struct)" 
      using STMap.prems(1) unfolding TypedStoSubpref.simps by blast
    moreover have "l \<noteq> x4" using STMap.prems(2) assms(3) by auto
    ultimately obtain i where idef:"typeCon x1 i \<and> TypedStoSubpref l (hash x4 i) struct" by blast
    then have iNoDot:" CHR ''.'' \<notin> set (literal.explode i)" using typeConNoDots[of x1 i] by blast
    then show ?case using idef TypedStoSubpref_child_imps_prnt 
      by (metis STMap.IH STMap.prems(2,3) TypedStoSubpref_sameLoc assms(3) TypedStoSubpref.simps(3))
  next
    case (STValue x)
    then show ?case by auto
  qed
qed


lemma CompStoType_same_type_same_depth:
  assumes "CompStoType tp'' t prnt l1"
    and "CompStoType tp'' t prnt' l2"
    and "location_depth  prnt = location_depth prnt'"
  shows "location_depth  l1 = location_depth l2" using assms 
proof(induction tp'' arbitrary: prnt prnt')
  case (STArray x1 tp'')
  obtain i where idef: "t = STArray x1 tp'' \<and> prnt = l1 
                        \<or> (i<x1 \<and> CompStoType tp'' t (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i)) l1)" 
    using STArray.prems unfolding  CompStoType.simps by blast
  obtain ii where iidef: "t = STArray x1 tp'' \<and> prnt' = l2 
                          \<or> (ii<x1 \<and> CompStoType tp'' t (hash prnt' (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) l2)" 
    using STArray.prems unfolding  CompStoType.simps by blast
  then show ?case 
  proof(cases "t = STArray x1 tp''")
    case True
    then show ?thesis using idef iidef STArray.prems(3) 
      using STArray.prems(1,2) comp_stotype_same_type_same_loc by blast
  next
    case False
    then have "CHR ''.'' \<notin> set (String.explode (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) \<and> CHR ''.'' \<notin> set (String.explode (ShowL\<^sub>n\<^sub>a\<^sub>t i))" 
      using ShowLNatDot iidef idef by auto
    then have "location_depth (hash prnt' (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) = location_depth (hash prnt' (ShowL\<^sub>n\<^sub>a\<^sub>t i))"
      using assms hash_adds_depth by metis
    then show ?thesis using STArray.IH False idef iidef 
      by (metis STArray.prems(3) location_depth_hash_property)
  qed
next
  case (STMap x1 tp'')
  obtain i where idef: "t = STMap x1 tp'' \<and> prnt = l1 \<or> 
                        (typeCon x1 i \<and> CompStoType tp'' t (hash prnt i) l1)"
    using STMap.prems unfolding  CompStoType.simps by blast
  obtain ii where iidef: "t = STMap x1 tp'' \<and> prnt' = l2 
                          \<or> (typeCon x1 ii \<and> CompStoType tp'' t (hash prnt' ii) l2)"
    using STMap.prems unfolding  CompStoType.simps by blast
  then show ?case 
  proof(cases "t = STMap x1 tp''")
    case True
    then show ?thesis using idef iidef STMap.prems(3) 
      using STMap.prems(1,2) comp_stotype_same_type_same_loc by blast
  next
    case False
    then have "CHR ''.'' \<notin> set (String.explode ii) \<and> CHR ''.'' \<notin> set (String.explode i)" 
      using typeConNoDots iidef idef by auto
    then have "location_depth (hash prnt' ii) = location_depth (hash prnt' i)"
      using assms hash_adds_depth by metis
    then show ?thesis using STMap.IH False idef iidef 
      by (metis STMap.prems(3) location_depth_hash_property)
  qed
next
  case (STValue x)
  then show ?case by auto
qed

lemma TypedStoSubpref_imp_same_depth:
  assumes "TypedStoSubpref l pa tp''"
    and "l \<noteq> pa"
  shows "\<exists>a. location_depth (hash pa a) = location_depth l" 
  using assms
proof(induction tp'' arbitrary:pa)
  case (STArray x1 tp'')
  then show ?case 
    using TypedStoSubpref_b by blast
next
  case (STMap x1 tp'')
  then show ?case 
    using TypedStoSubpref_b by blast
next
  case (STValue x)
  then show ?case by auto
qed

lemma same_depth_imp_neg_TypedStoSubpref:
  assumes "location_depth l = location_depth pa"
    and "l \<noteq> pa"
  shows "\<not>TypedStoSubpref l pa tp''" using assms TypedStoSubpref_imp_same_depth 
  by (metis add_less_same_cancel1 less_add_same_cancel1 less_nat_zero_code less_one location_depth_hash_property)


lemma CompStoType_unique_location:
  assumes "CompStoType struct tp1 (hash loc suffix1) p'"
    and "CompStoType struct tp2 (hash loc suffix2) p'"
    and "suffix1 \<noteq> suffix2"
    and "CHR ''.'' \<notin> set(String.explode suffix1)"
    and "CHR ''.'' \<notin> set(String.explode suffix2)"
  shows "False"
proof -
  have "hash loc suffix1 \<noteq> hash loc suffix2" using assms(3,4,5) hash_injective by blast
  moreover have "hash loc suffix1 = hash loc suffix2" using CompStoType_imps_subloc assms(1,2)
    by (metis CompStoType_imps_TypedStoSubpref NotRelatedPrnt_imps_notRelatedChild assms(4,5) hash_adds_depth
        same_depth_imp_neg_TypedStoSubpref)
  ultimately show ?thesis by simp
qed

lemma sublocs_nonchanged_SCon:
  assumes "\<not> TypedStoSubpref p' x4 struct"
    and "\<forall>locs t''.
       locs \<noteq> p' \<and> \<not> TypedStoSubpref locs p' (STArray x t''') \<longrightarrow>
       accessStorage t'' locs (storage st (address env)) = accessStorage t'' locs (storage st' (address env))"
    and "SCon struct x4 (storage st (address env))"
    and "\<not> TypedStoSubpref x4 p' (STArray x t''')"
  shows "SCon struct x4 (storage st' (address env))" using assms
proof(induction struct arbitrary:x4)
  case (STArray x1 struct)
  have a0:"\<forall>i<x1. SCon struct (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (storage st (address env))" 
    using STArray.prems(3) unfolding SCon.simps by simp
  moreover have "\<forall>i<x1. SCon struct (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (storage st' (address env))"
  proof intros
    fix i assume *:"i<x1"
    have "\<not> TypedStoSubpref p' (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) struct"
      using STArray.prems(1) * unfolding TypedStoSubpref.simps by auto
    moreover have "SCon struct (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (storage st (address env))" 
      using calculation * a0 by auto
    moreover have "\<not> TypedStoSubpref (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) p' (STArray x t''')"
    proof
      assume asm:"TypedStoSubpref (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) p' (STArray x t''')"
      have "hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<noteq> p'" using TypedStoSubpref_sameLoc asm 
        using calculation(1) by blast
      then have "TypedStoSubpref x4 p' (STArray x t''')" 
        using TypedStoSubpref_child_imps_prnt[OF asm _ ] ShowLNatDot by blast
      then show False using STArray.prems(4) by contradiction
    qed
    ultimately show "SCon struct (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (storage st' (address env))"
      using STArray.IH[of "hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)"] STArray.prems(2) by blast
  qed
  ultimately show ?case unfolding SCon.simps by simp
next
  case (STMap x1 struct)
  have t:"\<forall>i. typeCon x1 i \<longrightarrow> SCon struct (hash x4 i) (storage st (address env))" 
    using STMap.prems(3) unfolding SCon.simps by simp
  have "\<forall>i. typeCon x1 i \<longrightarrow> SCon struct (hash x4 i) (storage st' (address env))"
  proof intros
    fix i assume *:"typeCon x1 i"
    moreover have "\<not> TypedStoSubpref p' (hash x4 i) struct" 
      using STMap.prems(1) calculation by auto
    moreover have "\<forall>locs t''.
       locs \<noteq> p' \<and> \<not> TypedStoSubpref locs p' (STArray x t''') \<longrightarrow>
       accessStorage t'' locs (storage st (address env)) = accessStorage t'' locs (storage st' (address env))" 
      using STMap.prems(2) * by simp
    moreover have "SCon struct (hash x4 i) (storage st (address env))" using t * by blast
    moreover have "\<not> TypedStoSubpref (hash x4 i) p' (STArray x t''')" 
      using STMap.prems(4)  calculation(2) TypedStoSubpref_child_imps_prnt 
      using "*" TypedStoSubpref_sameLoc typeConNoDots by blast
    ultimately show "SCon struct (hash x4 i) (storage st' (address env))" using STMap.IH[of "(hash x4 i)"] by blast
  qed
  then show ?case unfolding SCon.simps by blast
next
  case (STValue x')
  have "typeCon x' (accessStorage x' x4 (storage st (address env)))" using STValue(3) unfolding SCon.simps by blast
  have "x4 \<noteq> p'" using STValue(1) by simp
  then have "(accessStorage x' x4 (storage st (address env))) = (accessStorage x' x4 (storage st' (address env)))" using STValue(2,4) by blast 
  then show ?case using \<open>typeCon x' (accessStorage x' x4 (storage st (address env)))\<close> by auto
qed


lemma singleLocChanged_nonchanged_SCon:
  assumes "\<forall>l. l \<noteq> locationChanged \<longrightarrow> storage st' (address env) $$ l = storage st (address env) $$ l"
    and "x4 \<noteq> locationChanged"
    and "SCon struct x4 (storage st (address env))"
    and "\<not> TypedStoSubpref l'' x4 struct"
    and "\<not> TypedStoSubpref x4 l'' t''"
    and " TypedStoSubpref locationChanged l'' t'' \<and> CompStoType t'' (STValue t') l'' locationChanged"
  shows " SCon struct x4 (storage st' (address env))" using assms(2,3,4,5,6)
proof(induction struct arbitrary:x4)
  case (STArray x1 struct)
  have asm2:"\<forall>i<x1. SCon struct (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (storage st (address env))" using STArray unfolding SCon.simps by auto
  have "\<forall>i<x1. SCon struct (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (storage st' (address env))"
  proof intros
    fix i assume asm3:"i<x1"
    then have "SCon struct (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (storage st (address env))" using asm2 by blast
    moreover have "(hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) \<noteq> locationChanged" using TypedStoSubpref_child_imps_prnt STArray.prems 
      using  asm3  ShowLNatDot   
      using TypedStoSubpref_sameLoc TypedStoSubpref.simps(2) by blast
    moreover have "\<not> TypedStoSubpref l'' (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) struct" using STArray.prems asm3 by simp
    moreover have "(hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) \<noteq> l''" 
      using TypedStoSubpref_sameLoc calculation(3) by auto
    moreover have "\<not> TypedStoSubpref (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) l'' t'' " using STArray.prems TypedStoSubpref_child_imps_prnt[of x4] asm3 ShowLNatDot 
      using calculation(4) by blast
    ultimately show "SCon struct (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (storage st' (address env))" using STArray(1)   STArray.prems(5)
      using assms(1) by auto
  qed
  then show ?case by simp
next
  case (STMap x1 struct)
  have asm2:"\<forall>i. typeCon x1 i \<longrightarrow> SCon struct (hash x4 i) (storage st (address env))" using STMap by auto
  have "\<forall>i. typeCon x1 i \<longrightarrow> SCon struct (hash x4 i) (storage st' (address env))"
  proof intros
    fix i assume asm3:"typeCon x1 i"
    then have "SCon struct (hash x4 i) (storage st (address env))" using asm2 by blast
    moreover have "hash x4 i \<noteq> locationChanged" using TypedStoSubpref_child_imps_prnt STMap 
      using asm3 typeConNoDots 
      by (metis TypedStoSubpref_sameLoc TypedStoSubpref.simps(3))
    moreover have "\<not> TypedStoSubpref l'' (hash x4 i) struct" using STMap asm3 by simp
    moreover have "hash x4 i \<noteq> l''" 
      using TypedStoSubpref_sameLoc calculation(3) by auto
    moreover have "\<not> TypedStoSubpref (hash x4 i) l'' t'' " using STMap.prems TypedStoSubpref_child_imps_prnt[of x4 i l'' t''] asm3 typeConNoDots 
      using calculation(4) by blast
    ultimately show "SCon struct (hash x4 i) (storage st' (address env))" using STMap(1)[of "(hash x4 i)"] STMap.prems(5)
      using assms(1) by auto
  qed
  then show ?case unfolding SCon.simps by simp
next
  case (STValue x)
  then show ?case using assms(1)
    by (simp add: accessStorage_def)
qed

lemma SCon_imps_sublocs:
  assumes "CompStoType t' struct l x2"
    and "SCon t' l (storage st' (address env))"
  shows "SCon struct x2 (storage st' (address env))"
  using assms 
proof(induction t' arbitrary: l)
  case (STArray x1 t''')
  have c:"struct = STArray x1 t''' \<and> l = x2 \<or> (\<exists>i<x1. CompStoType t''' struct (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) x2)" 
    using STArray.prems(1) unfolding CompStoType.simps by simp
  then show ?case 
  proof(cases "l = x2")
    case True
    then show ?thesis using c STArray 
      by auto
  next
    case False
    then show ?thesis using c STArray by auto
  qed
next
  case (STMap x1 t''')
  have c:"struct = STMap x1 t''' \<and> l = x2 \<or> (\<exists>i. typeCon x1 i \<and> CompStoType t''' struct (hash l i) x2)" 
    using STMap.prems(1) unfolding CompStoType.simps by simp
  then show ?case 
  proof(cases "l = x2")
    case True
    then show ?thesis 
      using CompStoType_sameLoc_sameType STMap.prems(1,2) by blast
  next
    case f1:False
    then obtain i where idef: "(typeCon x1 i \<and> CompStoType t''' struct (hash l i) x2)"
      using c by blast
    then show ?thesis using STMap.IH 
      using STMap.prems(2) by auto
  qed
next
  case (STValue x)
  then show ?case by auto
qed


lemma php1:
  assumes "TypedStoSubpref lc l'' t''"
    and "TypedStoSubpref lc x4 struct"
  shows "\<exists>pref. hash l'' pref = x4 \<or> hash x4 pref = l'' \<or> l'' =x4 "
proof -
  obtain pre1 where a10: "hash l'' pre1 = lc \<or> lc = l''" using TypedStoSubpref_b assms by blast
  obtain pre2 where a20:"hash x4 pre2 = lc \<or> lc = x4" using assms TypedStoSubpref_b by blast
  then show ?thesis 
  proof (cases "pre1 = pre2")
    case True
    then show ?thesis using a10 a20 hash_never_equal_prefix by auto
  next
    case False
    then show ?thesis by (metis LSubPrefL2_def a10 a20 Mutual_NonSub_SpecificNonSub)
  qed
qed



lemma subLocs:
  assumes "SCon struct x4 (storage st (address env))"
    and "\<forall>l struct. \<not>TypedStoSubpref locationChanged l struct \<longrightarrow>  storage st' (address env) $$ l = storage st (address env) $$ l"
    and "(\<forall>i'. (hash x4 i') \<noteq> locationChanged)"
    and "x4 \<noteq> locationChanged"
  shows " SCon struct x4 (storage st' (address env))" using assms(2) assms(1) assms(3) assms(4) 
proof(induction struct arbitrary: x4)
  case (STArray x1 struct)
  have "(\<forall>i<x1. SCon struct (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (storage st' (address env)))"
  proof(intros)
    fix i assume iless:"i<x1" 
    then have "SCon struct (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (storage st (address env))" using STArray(3) by simp
    moreover have "\<forall>l struct. \<not> TypedStoSubpref locationChanged l struct \<longrightarrow> storage st' (address env) $$ l = storage st (address env) $$ l" using STArray by auto
    moreover have " \<forall>i'. hash (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) i' \<noteq> locationChanged" using STArray by (simp add: hash_suffixes_associative)
    moreover have "hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<noteq> locationChanged" using STArray by blast
    ultimately show "SCon struct (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (storage st' (address env)) " using STArray(1)[of "(hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i))"]  by blast
  qed
  then show ?case using SCon.simps(2)[of x1 struct x4 "(storage st' (address env))"] by auto
next
  case (STMap x1 struct)
  have "(\<forall>i. typeCon x1 i \<longrightarrow> SCon struct (hash x4 i) (storage st' (address env)))"
  proof intros
    fix i assume *:"typeCon x1 i"
    then have "SCon struct (hash x4 i) (storage st (address env))" using STMap(3) by simp
    moreover have "\<forall>l struct. \<not> TypedStoSubpref locationChanged l struct \<longrightarrow> storage st' (address env) $$ l = storage st (address env) $$ l" using STMap by auto
    moreover have " \<forall>i'. hash (hash x4 i) i' \<noteq> locationChanged" using STMap by (simp add: hash_suffixes_associative)
    moreover have "hash x4 i \<noteq> locationChanged" using STMap by blast
    ultimately show "SCon struct (hash x4 i) (storage st' (address env)) " using STMap(1)[of "(hash x4 i)"]  by blast
  qed
  then show ?case using SCon.simps(3)[of x1 struct x4 "(storage st' (address env))"] by simp
next
  case (STValue x)
  have "typeCon x (accessStorage x x4 (storage st' (address env)))" unfolding accessStorage_def using STValue(1) STValue(2)  STValue(4)
    by (metis accessStorage_def SCon.simps(1) TypedStoSubpref.simps(1))
  then show ?case using SCon.simps(1)[of x x4 "(storage st' (address env))"] by auto
qed



lemma stvalueLocationsInduct:
  assumes "CompStoType struct (STValue t') x4 locationChanged"
    and   " SCon struct x4 (storage st (address env))"
    and  "SCon (STValue t') locationChanged (storage st' (address env))"
    and  "hash x4 i'' = locationChanged"
    and "\<forall>l struct. \<not>TypedStoSubpref locationChanged l struct \<longrightarrow>  storage st' (address env) $$ l = storage st (address env) $$ l"
    and "\<forall>l. l \<noteq> locationChanged \<longrightarrow> storage st' (address env) $$ l = storage st (address env) $$ l" 
  shows "SCon struct x4 (storage st' (address env))" using assms(1) assms(2) assms(3) assms(4) assms(5)
proof(induction struct arbitrary:x4 i'')
  case (STArray x1 struct)
  then have c5:" ((\<exists>i<x1. CompStoType struct (STValue t') (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) locationChanged))"
    using CompStoType.simps(2)[of x1 struct "(STValue t')" x4 locationChanged]  by auto
  have "(\<forall>i<x1. SCon struct (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (storage st' (address env)))"
  proof intros
    fix i assume iless:"i<x1"
    show "SCon struct (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (storage st' (address env)) "
    proof(cases "(ShowL\<^sub>n\<^sub>a\<^sub>t i) = i''")
      case True
      then have "locationChanged = (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i))" by (simp add: STArray.prems)
      moreover have "struct = (STValue t')" 
        using c5 True iless CompStoType_sameLoc_sameType CompStoType_imps_subloc STArray.prems(4) ShowLNatDot
        by (metis LSubPrefL2_def typeCon_no_sublocation_prefix checkAddress_def typeCon.simps(4))
      ultimately have "SCon struct locationChanged (storage st' (address env))" 
        using STArray by auto
      then show ?thesis using STArray True by simp
    next
      case False
      then have c10:"SCon struct (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (storage st (address env))" using STArray iless by simp
      have c20:"hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<noteq> locationChanged" using False STArray.prems hash_never_equal_sufix by auto
      have c30:" SCon (STValue t') locationChanged (storage st' (address env))" using STArray(4) by auto
      then show ?thesis 
      proof(cases " CompStoType struct (STValue t') (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) locationChanged")
        case True
        then show ?thesis using STArray(1) c10 c20 c30 False 
          by (meson CompStoType_imps_subloc STArray.prems(3) STArray(6))
      next
        case False
        then have "(\<forall>i'. (hash (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) i') \<noteq> locationChanged)" 
          using False by (metis (full_types) CompStoType_imps_subloc c5 hash_suffixes_associative hashesInts)
        then show ?thesis using subLocs[of struct "(hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i))" st env locationChanged st']  c10 STArray(6) c20 False by auto 
      qed
    qed
  qed
  then show ?case using SCon.simps(2)[of x1 struct x4 "(storage st' (address env))"] by simp
next
  case (STMap x1 struct)
  then have c5:" ((\<exists>i. typeCon x1 i \<and>  CompStoType struct (STValue t') (hash x4 i) locationChanged))"
    using CompStoType.simps(3)[of x1 struct "(STValue t')" x4 locationChanged] by simp
  then obtain i''' where i'''def:" typeCon x1 i''' \<and>  CompStoType struct (STValue t') (hash x4 i''') locationChanged" by auto
  have "(\<forall>i. typeCon x1 i \<longrightarrow> SCon struct (hash x4 i) (storage st' (address env)))"
  proof intros
    fix i assume iless:"typeCon x1 i"
    show "SCon struct (hash x4 i) (storage st' (address env)) "
    proof(cases "i = i''")
      case t9:True
      then have locsSame:"locationChanged = (hash x4 i)" 
        by (simp add: STMap.prems(4))
      then have "struct = (STValue t')" 
        using c5 t9  iless locsSame CompStoType_sameLoc_sameType[of struct "STValue t'" "hash x4 i"] 
        by (metis CompStoType_imps_subloc LSubPrefL2_def typeCon_no_sublocation_prefix)
      then have "SCon struct locationChanged (storage st' (address env))" 
        using STMap(4) by auto
      then show ?thesis using STMap t9 by force
    next
      case f3:False
      then have c10:"SCon struct (hash x4 i) (storage st (address env))" using STMap iless by simp
      have c20:"hash x4 i \<noteq> locationChanged" using f3 STMap.prems(4) hash_never_equal_sufix by auto
      have c30:"SCon (STValue t') locationChanged (storage st' (address env))" using STMap(4) by auto
      then show ?thesis 
      proof(cases " CompStoType struct (STValue t') (hash x4 i) locationChanged")
        case True
        then show ?thesis using STMap(1) c10 c20 c30 f3 

          by (meson CompStoType_imps_subloc STMap(6))
      next
        case False
        then have "(\<forall>i'. (hash (hash x4 (i)) i') \<noteq> locationChanged)" using c5 Mutual_NonSub_SpecificNonSub
          using False f3 iless typeCon_no_sublocation_prefix i'''def c10  CompStoType_imps_subloc 
          by (smt (verit, best) LSubPrefL2_def) 
        then show ?thesis using subLocs[of struct "(hash x4 i)" st env locationChanged st']  c10 STMap(6) c20 False by auto 
      qed
    qed
  qed
  then show ?case using SCon.simps(3)[of x1 struct x4 "(storage st' (address env))"] by simp
next
  case (STValue x)
  then show ?case using SCon.simps(1)[of x x4 "(storage st' (address env))"] assms(6)  by simp
qed

lemma CompLocs_imp_typs:
  assumes "CompStoType t'' struct l'' x4"
    and "CompStoType t'' (STValue t') l'' x4"
  shows "struct = STValue t'" using assms 
proof(induction t'' arbitrary:l'')
  case (STArray x1 t'')
  then show ?case 
  proof(cases "l'' = x4")
    case True
    then show ?thesis using STArray 
      using CompStoType_sameLoc_sameType by blast
  next
    case False
    then obtain z where a10:"hash l'' z = x4" using STArray CompStoType_imps_subloc by blast
    obtain i where  a20:"(i<x1 \<and> CompStoType t'' struct (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) x4)" 
      using STArray(2) CompStoType.simps(2)[of x1 t'' struct l'' x4] False by blast
    obtain i' where  a30:"(i'<x1 \<and> CompStoType t'' (STValue t') (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i')) x4)" 
      using STArray(3) CompStoType.simps(2)[of x1 t'' "STValue t'" l'' x4] False by blast
    then show ?thesis using STArray(1)[of "(hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i))"] using a30 a20 ShowLNatDot
      by (metis CompStoType_imps_subloc LSubPrefL2_def hash_int_prefix hashesInts)
  qed
next
  case (STMap x1 t'')
  then show ?case 
  proof(cases "l'' = x4")
    case True
    then show ?thesis using STMap 
      using CompStoType_sameLoc_sameType by blast
  next
    case False
    then obtain z where a10:"hash l'' z = x4" using STMap CompStoType_imps_subloc by blast
    obtain i where  a20:"(typeCon x1 i \<and> CompStoType t'' struct (hash l'' i) x4)" 
      using STMap(2) CompStoType.simps(3)[of x1 t'' struct l'' x4] False by blast
    then have a25:"CHR ''.'' \<notin> set(String.explode i)" using typeConNoDots by auto
    obtain i' where  a30:"( typeCon x1 i' \<and> CompStoType t'' (STValue t') (hash l'' i') x4)" 
      using STMap(3) CompStoType.simps(3)[of x1 t'' "STValue t'" l'' x4] False by blast
    then have a35:"CHR ''.'' \<notin> set(String.explode i')" using typeConNoDots by auto
    then show ?thesis
    proof(cases "hash l'' i' = x4")
      case True
      then have "t'' = STValue t'" using a30 
        using CompStoType_sameLoc_sameType by auto 
      then show ?thesis using a20 by simp
    next
      case False
      then have b10:"\<exists>c. hash (hash l'' i') c = x4" using a30 CompStoType_imps_subloc by auto
      then have b20:"\<exists>c. hash (hash l'' i) c = x4" using False a20 CompStoType_imps_subloc a25 
        by (metis LSubPrefL2_def typeCon_no_sublocation_prefix)
      then have "i'=i" using b10 b20 
        using a25 a35 hashesAssociative by blast
      then show ?thesis  using STMap(1) using a30 a20 a25 a35 by auto
    qed
  qed
next
  case (STValue x)
  then show ?case by simp
qed

lemma CompStoType_imp_subStoTp:
  shows "CompStoType t'' t' l'' l' \<longrightarrow> subStoTp t' t''"
proof(induction t'' arbitrary:l'')
  case (STArray x1 t'')
  show ?case
  proof
    assume *:"CompStoType (STArray x1 t'') t' l'' l'"
    show "subStoTp t' (STArray x1 t'')"
    proof(cases "STArray x1 t'' = t'")
      case True
      then show ?thesis by auto
    next
      case False
      then show ?thesis using *  CompStoType.simps(2) STArray by auto
    qed
  qed
next
  case (STMap x1 t'')
  show ?case 
  proof
    assume *:"CompStoType (STMap x1 t'') t' l'' l'"
    then show "subStoTp t' (STMap x1 t'')" 
    proof(cases "t' = (STMap x1 t'')")
      case True
      then show ?thesis by simp
    next
      case False
      then have "(\<exists>i. typeCon x1 i \<and> CompStoType t'' t' (hash l'' i) l')" 
        using CompStoType.simps(3)[of x1 t'' t' l'' l'] * by auto
      then show ?thesis using STMap(1) by auto
    qed
  qed
next
  case (STValue x)
  then show ?case by simp
qed

lemma subStoType_trans:
  assumes "subStoTp t'  t''"
    and "subStoTp (STValue t''') t''"
  shows "subStoTp  (STValue t''') t'" using assms 
proof(induction t')
  case (STArray x1 t')
  then show ?case
  proof(induction t'')
    case (STArray x1 t'')
    then show ?case by auto
  next
    case (STMap x1 t'')
    then show ?case by simp
  next
    case (STValue x)
    then show ?case by simp
  qed
next
  case (STMap x1 t')
  then show ?case 
  proof(induction t'')
    case (STArray x1 t'')
    then show ?case by auto
  next
    case (STMap x1 t'')
    then show ?case by auto
  next
    case (STValue x)
    then show ?case by simp
  qed
next
  case (STValue x)
  then show ?case 
  proof(induction t'')
    case (STArray x1 t'')
    then show ?case by simp
  next
    case (STMap x1 t'')
    then show ?case by simp
  next
    case (STValue x')
    then show ?case by simp
  qed
qed

lemma tap:
  assumes "CompStoType t'' (STValue t') l'' locationChanged "
    and" CompStoType t'' struct l'' x4 "
    and "TypedStoSubpref locationChanged x4 struct"
  shows " CompStoType struct (STValue t') x4 locationChanged" using assms
proof(induction t'' arbitrary:l'')
  case (STArray x1 t'')
  then show ?case 
  proof(cases "l'' = locationChanged")
    case True
    then show ?thesis using STArray using CompStoType_sameLoc_sameType by blast
  next
    case f1:False
    then show ?thesis 
    proof(cases "l'' = x4")
      case True
      then show ?thesis using STArray f1 using CompStoType_sameLoc_sameType by blast
    next
      case False
      then obtain i1 where a10:"(i1<x1 \<and> CompStoType t'' (STValue t') (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) locationChanged)" 
        using STArray(2) CompStoType.simps(2)[of x1 t'' "STValue t'" l'' locationChanged] using f1 by blast
      then obtain i2 where a20:" (i2<x1 \<and> CompStoType t'' struct (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) x4)"         
        using STArray(3) CompStoType.simps(2)[of x1 t'' "struct" l'' x4] using False by blast
      then have a30:"i1 = i2" using a10 a20 STArray 
      proof -
        obtain ll :: "String.literal \<Rightarrow> String.literal \<Rightarrow> String.literal" where
          f1: "\<forall>l la s sa. hash l (ll la l) = la \<or> \<not> CompStoType s sa l la \<or> l = la"
          by (metis (no_types) CompStoType_imps_subloc)
        obtain lla :: "String.literal \<Rightarrow> String.literal \<Rightarrow> String.literal" where
          f2: "locationChanged = hash x4 (lla x4 locationChanged) \<or> x4 = locationChanged"
          using TypedStoSubpref_b assms(3) by fastforce
        then have f3: "\<forall>l. hash x4 (hash (lla x4 locationChanged) l) = hash locationChanged l \<or> x4 = locationChanged"
          by (metis hash_suffixes_associative)
        have f4: "x4 = hash (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) (ll x4 (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i2))) \<or> x4 = hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i2)"
          using f1 by (metis (full_types) a20)
        have f5: "locationChanged = hash (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) (ll locationChanged (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i1))) \<or> locationChanged = hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i1)"
          using f1 by (metis a10)
        have f6: "\<forall>l. hash x4 l = hash (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) (hash (ll x4 (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i2))) l) \<or> x4 = hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i2)"
          using f4 by (metis hash_suffixes_associative)
        have f7: "\<forall>l n. locationChanged \<noteq> hash (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t n)) l \<or> i1 = n \<or> locationChanged = hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i1)"
          using f5 by (meson hashesInts)
        { assume "\<exists>l la. hash locationChanged l = hash locationChanged la \<and> i2 \<noteq> i1"
          { assume "\<exists>l la. hash locationChanged la = hash locationChanged l \<and> x4 \<noteq> locationChanged"
            moreover
            { assume "\<exists>l la. hash locationChanged la = hash x4 l \<and> i2 \<noteq> i1 \<and> x4 \<noteq> locationChanged"
              moreover
              { assume "\<exists>l la. hash locationChanged la = hash locationChanged l \<and> x4 \<noteq> hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i2) \<and> x4 \<noteq> locationChanged"
                then have "locationChanged \<noteq> hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i1) \<and> x4 \<noteq> locationChanged \<or> i1 = i2"
                  using f6 f3 by (metis (no_types) hashesInts) }
              ultimately have "x4 \<noteq> hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i2) \<and> locationChanged \<noteq> hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i1) \<or> i1 = i2"
                using f7 f2 by (metis (no_types) hashesInts) }
            ultimately have "x4 \<noteq> hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i2) \<and> locationChanged \<noteq> hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i1) \<or> i1 = i2"
              using f3 by (metis (full_types)) }
          then have ?thesis
            using f5 f4 f2 by (metis hash_suffixes_associative hashesInts) }
        then show ?thesis
          by blast
      qed

      then show ?thesis 
      proof(cases "x4 = locationChanged")
        case True
        then show ?thesis 
          using STArray.IH a10 a20 a30 assms(3) by auto
      next
        case False
        then show ?thesis 
          using STArray.IH a10 a20 a30 assms(3) by auto
      qed
    qed
  qed
next
  case (STMap x1 t'')
  then show ?case 
  proof(cases "l'' = locationChanged")
    case True
    then show ?thesis using STMap using CompStoType_sameLoc_sameType by blast
  next
    case f1:False
    then show ?thesis 
    proof(cases "l'' = x4")
      case True
      then show ?thesis using STMap f1 using CompStoType_sameLoc_sameType by blast
    next
      case False
      then obtain i1 where a10:"(typeCon x1 i1 \<and> CompStoType t'' (STValue t') (hash l'' i1) locationChanged)" 
        using STMap(2) CompStoType.simps(3)[of x1 t'' "STValue t'" l'' locationChanged] using f1 by blast
      then obtain i2 where a20:" (typeCon x1 i2 \<and> CompStoType t'' struct (hash l'' i2) x4)"         
        using STMap(3) CompStoType.simps(3) using False by blast
      have a30:"CHR ''.'' \<notin> set(String.explode i1)" using a10 using typeConNoDots by auto
      have a40:"CHR ''.'' \<notin> set(String.explode i2)" using a20 using typeConNoDots by auto

      then have a30:"i1 = i2" using a10 a20 STMap
        by (smt (verit, ccfv_threshold) CompStoType_imps_subloc LSubPrefL2_def typeCon_no_sublocation_prefix TypedStoSubpref_b hash_suffixes_associative hashesAssociative typeConNoDots)

      then show ?thesis 
      proof(cases "x4 = locationChanged")
        case True
        then show ?thesis 
          using STMap.IH a10 a20 a30 assms(3) by auto
      next
        case False
        then show ?thesis 
          using STMap.IH a10 a20 a30 assms(3) by auto
      qed
    qed
  qed
next
  case (STValue x)
  then show ?case by simp
qed

lemma CompStoType_sameLocs_sameType:
  assumes "CompStoType t t' l''' x4"
    and "CompStoType t struct l''' x4"
  shows "struct = t'" using assms
proof(induction t arbitrary:l''')
  case (STArray x1 t)
  have asm1:"t' = STArray x1 t \<and> l''' = x4 \<or> (\<exists>i<x1. CompStoType t t' (hash l''' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) x4)" 
    using STArray.prems unfolding CompStoType.simps by simp
  have asm2:"struct = STArray x1 t \<and> l''' = x4 \<or> (\<exists>i<x1. CompStoType t struct (hash l''' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) x4)" 
    using STArray.prems unfolding CompStoType.simps by simp
  then show ?case 
  proof(cases "l''' = x4")
    case True
    then have "t' = STArray x1 t " using asm1 asm2 
      using CompStoType_sameLoc_sameType STArray.prems assms by blast
    moreover have "struct = STArray x1 t " using asm1 asm2 
      using CompStoType_sameLoc_sameType STArray.prems True by blast
    ultimately show ?thesis by blast
  next
    case False
    then have "(\<exists>i<x1. CompStoType t t' (hash l''' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) x4)" using asm1 by simp
    moreover have "(\<exists>i<x1. CompStoType t struct (hash l''' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) x4)" using asm2 False by simp
    ultimately show ?thesis using STArray.IH 
      using CompStoType_unique_location typeConNoDots 
      by (metis ShowLNatDot)
  qed
next
  case (STMap x1 t)
  have asm1:"t' = STMap x1 t \<and> l''' = x4 \<or> (\<exists>i. typeCon x1 i \<and> CompStoType t t' (hash l''' i) x4)" 
    using STMap.prems unfolding CompStoType.simps by simp
  have asm2:"struct = STMap x1 t \<and> l''' = x4 \<or> (\<exists>i. typeCon x1 i \<and> CompStoType t struct (hash l''' i) x4)" 
    using STMap.prems unfolding CompStoType.simps by simp
  then show ?case 
  proof(cases "l''' = x4")
    case True
    then have "t' = STMap x1 t" using asm1 asm2 
      using CompStoType_sameLoc_sameType STMap.prems assms by blast
    moreover have "struct = STMap x1 t " using asm1 asm2 
      using CompStoType_sameLoc_sameType STMap.prems True by blast
    ultimately show ?thesis by blast
  next
    case False
    then have "(\<exists>i. typeCon x1 i \<and> CompStoType t t' (hash l''' i) x4)" using asm1 by simp
    moreover have "(\<exists>i. typeCon x1 i \<and> CompStoType t struct (hash l''' i) x4)" using asm2 False by simp
    ultimately show ?thesis using STMap.IH 
      using CompStoType_unique_location typeConNoDots by blast
     
  qed
next
  case (STValue x)
  then show ?case by simp
qed




lemma CompStoType_trns:
  assumes "CompStoType struct t'' x4 l''"
    and "CompStoType t'' t' l'' locationChanged"
  shows "CompStoType struct t' x4 locationChanged" using assms
proof(induction struct arbitrary:x4)
  case (STArray x1 struct)
  show ?case

  proof(cases "x4 = l''")
    case True
    then have "t'' = STArray x1 struct" using STArray.prems CompStoType_sameLoc_sameType by blast
    then have "CompStoType (STArray x1 struct) t' x4 locationChanged" using STArray.prems True by simp
    then show ?thesis by simp
  next
    case False
    then have "(\<exists>i<x1. CompStoType struct t'' (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) l'')" 
      using STArray.prems CompStoType.simps(2)[of x1 struct t'' x4 l''] by simp
    then obtain i where a10:"i<x1 \<and> CompStoType struct t'' (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) l''" by auto
    then have "CompStoType struct t' (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) locationChanged" using STArray STArray.prems by simp
    then have " (\<exists>i<x1. CompStoType struct t' (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) locationChanged)" using a10 by auto
    then show ?thesis by simp
  qed      

next
  case (STMap x1 struct)
  show ?case

  proof(cases "x4 = l''")
    case True
    then have "t'' = STMap x1 struct" using STMap.prems CompStoType_sameLoc_sameType by blast
    then have "CompStoType (STMap x1 struct) t' x4 locationChanged" using STMap.prems True by simp
    then show ?thesis by simp
  next
    case False
    then have "(\<exists>i. typeCon x1 i \<and> CompStoType struct t'' (hash x4 i) l'')" 
      using STMap.prems CompStoType.simps(3)[of x1 struct t'' x4 l''] by simp
    then obtain i where a10:"typeCon x1 i \<and> CompStoType struct t'' (hash x4 i) l''" by auto
    then have "CompStoType struct t' (hash x4 i) locationChanged" using STMap STMap.prems by simp
    then have " (\<exists>i. typeCon x1 i \<and> CompStoType struct t' (hash x4 i) locationChanged)" using a10 by auto
    then show ?thesis by simp
  qed

next
  case (STValue x)
  then show ?case by auto
qed

lemma NotReachablePrnt_imps_notReachableChild:
  assumes "\<not> TypedStoSubpref x4 l''' t"
    and "\<not> TypedStoSubpref l''' x4 struct" 
    and "CompStoType t t' l''' l"
  shows "\<not> TypedStoSubpref x4 l t'" 
proof
  assume asm1:"TypedStoSubpref x4 l t'"
  show False using asm1 assms
  proof(induction t' arbitrary:l l''')
    case (STArray x1 struct)
    have asm2:"x4 = l \<or> (\<exists>i<x1. TypedStoSubpref x4 (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) struct)" 
      using STArray.prems(1) unfolding TypedStoSubpref.simps by blast
    then show ?case
    proof(cases "x4 = l")
      case True
      then show ?thesis 
        using CompStoType_imps_TypedStoSubpref STArray.prems by auto
    next
      case False
      then obtain i where idef:"(i<x1 \<and> TypedStoSubpref x4 (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) struct)" using asm2 by auto
      then have asm4:"CompStoType (STArray x1 struct) struct l (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i))" 
        using CompStoType_sameLocNdTyp by auto 
      then have iNoDot:" CHR ''.'' \<notin> set (literal.explode (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using idef ShowLNatDot by blast

      then show ?thesis 
      proof(cases "l = l'''")
        case True
        then show ?thesis 
          using CompStoType_sameLoc_sameType STArray.prems by blast
      next
        case False
        then have "CompStoType t struct l''' (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) " using idef STArray.prems asm4 
          using CompStoType_trns by blast
        then show ?thesis using STArray.IH STArray.prems(2,3) idef by blast
      qed
    qed
  next
    case (STMap x1 struct)
    have asm2:"x4 = l \<or> (\<exists>i. typeCon x1 i \<and> TypedStoSubpref x4 (hash l i) struct)" 
      using STMap.prems(1) unfolding TypedStoSubpref.simps by blast
    then show ?case
    proof(cases "x4 = l")
      case True
      then show ?thesis 
        using CompStoType_imps_TypedStoSubpref STMap.prems(4) assms(1) 
        using STMap.prems(2) by auto
    next
      case False
      then obtain i where idef:"(typeCon x1 i \<and> TypedStoSubpref x4 (hash l i) struct)" using asm2 by auto
      then have asm4:"CompStoType (STMap x1 struct) struct l (hash l i)" 
        using CompStoType_sameLocNdTyp by auto 
      then have iNoDot:" CHR ''.'' \<notin> set (literal.explode i)" using idef typeConNoDots[of x1 i] by blast

      then show ?thesis 
      proof(cases "l = l'''")
        case True
        then show ?thesis 
          using CompStoType_sameLoc_sameType STMap.prems(1,4) 
          using STMap.prems(2) by blast
      next
        case False
        then have "CompStoType t struct l''' (hash l i) " using idef STMap.prems(4) asm4 
          using CompStoType_trns by blast
        then show ?thesis using STMap.IH STMap.prems(2,3) idef by blast
      qed
    qed
  next
    case (STValue x)
    then have "x4 = l" unfolding TypedStoSubpref.simps by simp
    then have "CompStoType t (STValue x) l''' x4" using STValue by blast
    then have "TypedStoSubpref x4 l''' t"
      using CompStoType_imps_TypedStoSubpref[of t _ l''' x4] by simp
    then show ?case using STValue by simp
  qed
qed

lemma SCon_noDots:
  assumes "SCon tp (hash destl i) v'"
    and "\<forall>i' t.  accessStorage t (hash (hash destl i) i') v' = accessStorage t (hash (hash destl i) i') v''"
    and " \<forall>t. accessStorage t (hash destl i) v' = accessStorage t (hash destl i) v''"
    and "CHR ''.'' \<notin> set(String.explode i)"
  shows "SCon tp (hash destl i) v''" using assms
proof (induction tp arbitrary: destl i)
  case (STArray x1 tp)

  have " \<forall>i'<x1. SCon tp (hash (hash destl i) (ShowL\<^sub>n\<^sub>a\<^sub>t i')) v''"
  proof intros
    fix i' assume *:"i'<x1"
    then have "SCon tp (hash (hash destl i) (ShowL\<^sub>n\<^sub>a\<^sub>t i')) v'" using STArray.prems by simp
    moreover  have "\<forall>i'a t. accessStorage t (hash (hash (hash destl i) (ShowL\<^sub>n\<^sub>a\<^sub>t i')) i'a) v' = accessStorage t (hash (hash (hash destl i) (ShowL\<^sub>n\<^sub>a\<^sub>t i')) i'a) v''" using STArray.prems 
      by (simp add: hash_suffixes_associative)
    moreover have "CHR ''.'' \<notin> set (literal.explode (ShowL\<^sub>n\<^sub>a\<^sub>t i'))" using ShowLNatDot by simp
    moreover have "\<forall>t. accessStorage t (hash (hash destl i) (ShowL\<^sub>n\<^sub>a\<^sub>t i')) v' = accessStorage t (hash (hash destl i) (ShowL\<^sub>n\<^sub>a\<^sub>t i')) v''" using STArray.prems by simp
    ultimately show "SCon tp (hash (hash destl i) (ShowL\<^sub>n\<^sub>a\<^sub>t i')) v''" using STArray.IH[of "(hash destl i)" "(ShowL\<^sub>n\<^sub>a\<^sub>t i')"] by blast
  qed
  then show ?case unfolding SCon.simps by simp
next
  case (STMap x1 tp)
  have "\<forall>i'. typeCon x1 i' \<longrightarrow> SCon tp (hash (hash destl i) i') v''"
  proof intros
    fix i' assume *:"typeCon x1 i'"
    then have "CHR ''.'' \<notin> set (literal.explode i')" using typeConNoDots by simp
    moreover have "SCon tp (hash (hash destl i) i') v'" using * STMap.prems by simp
    moreover  have "\<forall>i'a t. accessStorage t (hash (hash (hash destl i) i') i'a) v' = accessStorage t (hash (hash (hash destl i) i') i'a) v''" using STMap.prems 
      by (simp add: hash_suffixes_associative)
    moreover have "\<forall>t. accessStorage t (hash (hash destl i) i') v' = accessStorage t (hash (hash destl i) i') v''" using STMap.prems by simp
    ultimately  show "SCon tp (hash (hash destl i) i') v''" using STMap.IH by blast
  qed
  then show ?case unfolding SCon.simps by simp
next
  case (STValue x)
  then show ?case by auto
qed

lemma Sto_divergence_imps_notsubloc:
  shows "\<not>TypedStoSubpref (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) destl (STArray x tp)"
proof
  assume "TypedStoSubpref (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) destl (STArray x tp)"
  then have *:"hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x) = destl \<or> (\<exists>i<x. TypedStoSubpref (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) tp)"
    unfolding TypedStoSubpref.simps by simp
  then have "hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x) \<noteq> destl" using ShowLNatDot 
    using hash_inequality by auto
  then obtain i where asm4:"(i<x \<and> TypedStoSubpref (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) tp)" 
    using * by blast
  then show False
  proof (cases tp)
    case (STArray x1 tp)
    have *:" i < x \<and> (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x) = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i) 
\<or> (\<exists>ia. ia <x1 \<and> TypedStoSubpref (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (ShowL\<^sub>n\<^sub>a\<^sub>t ia)) tp))" 
      using asm4 STArray unfolding TypedStoSubpref.simps by simp
    then have "hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x) \<noteq> hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)" using hash_injective ShowLNatDot  Read_Show_nat'_id readLintNotEqual * by metis
    then obtain ia where " ia <x1 \<and> TypedStoSubpref (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (ShowL\<^sub>n\<^sub>a\<^sub>t ia)) tp" using * by auto
    then have a3:"TypedStoSubpref (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (ShowL\<^sub>n\<^sub>a\<^sub>t ia)) tp" 
      by (simp add: hash_suffixes_associative)
    then have " (hash (ShowL\<^sub>n\<^sub>a\<^sub>t i) (ShowL\<^sub>n\<^sub>a\<^sub>t ia)) \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t x)" using hash_def ShowLNatDot 
      by (metis subPrefCannotBeInt)
    then show ?thesis using a3 hash_injective ShowLNatDot TypedStoSubpref_child_imps_prnt TypedStoSubpref_hashes hash_never_equal_sufix
      by (metis asm4)
  next
    case (STMap x1 tp)
    have *:" i < x \<and> (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x) = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<or> (\<exists>ia. typeCon x1 ia 
          \<and> TypedStoSubpref (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) ia) tp))" 
      using asm4 STMap unfolding TypedStoSubpref.simps by simp
    then have "hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x) \<noteq> hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)" using hash_injective ShowLNatDot  Read_Show_nat'_id readLintNotEqual * by metis
    then obtain ia where "(typeCon x1 ia \<and> TypedStoSubpref (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) ia) tp)" using * by auto
    then have a3:"TypedStoSubpref (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (hash (ShowL\<^sub>n\<^sub>a\<^sub>t i) ia)) tp" 
      by (simp add: hash_suffixes_associative)
    then have " (hash (ShowL\<^sub>n\<^sub>a\<^sub>t i) ia) \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t x)" using hash_def ShowLNatDot 
      by (metis subPrefCannotBeInt)
    then show ?thesis using a3 hash_injective ShowLNatDot 
      by (metis TypedStoSubpref_child_imps_prnt TypedStoSubpref_hashes hash_never_equal_sufix)
  next
    case (STValue x')
    then have **:"i < x \<and> hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x) = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)" unfolding TypedStoSubpref.simps using asm4 by simp
    then have "(ShowL\<^sub>n\<^sub>a\<^sub>t x) = (ShowL\<^sub>n\<^sub>a\<^sub>t i)" using hash_injective ShowLNatDot by blast
    then show ?thesis using ** 
      by (metis Read_Show_nat'_id readLintNotEqual)
  qed
qed



lemma NoSubChanged_Scon_Preserved:
  assumes "SCon t'  destl srcMem"
    and "\<forall>i' t''. accessStorage t'' (hash destl i') srcMem = accessStorage t'' (hash destl i') v'"
    and "\<forall>t''. accessStorage t'' destl srcMem = accessStorage t'' destl v'"
  shows "SCon t'  destl v'" using assms
proof(induction t' arbitrary: destl)
  case (STArray x1 t')
  then show ?case 
    by (simp add: hash_suffixes_associative)
next
  case (STMap x1 t')
  then show ?case 
    by (simp add: hash_suffixes_associative)
next
  case (STValue x)
  then show ?case by simp
qed




lemma Scon_NoChange:
  assumes "\<forall>destl'. TypedStoSubpref destl' destl t' \<longrightarrow> (\<forall>t. accessStorage t destl' srcMem = accessStorage t destl' v')"
    and "SCon t' destl srcMem"
  shows "SCon t' destl v'" using assms
proof(induction t' arbitrary:destl)
  case (STArray x1 t')
  then show ?case 
    by (meson SCon.simps(2) TypedStoSubpref.simps(2))
next
  case (STMap x1 t')
  then show ?case 
    by (meson SCon.simps(3) TypedStoSubpref.simps(3))
next
  case (STValue x)
  then show ?case by simp
qed

lemma subloc_deeper:
  assumes "TypedStoSubpref p l t"
    and "p\<noteq>l"
  shows "location_depth p > location_depth l" using assms 
  by (metis Suc_eq_plus1 TypedStoSubpref_b location_depth_hash_property not_add_less1 not_less_eq)

lemma TypedStoSubpref_arr_longer:
  assumes "(\<forall>subL. TypedStoSubpref subL srcl (STArray (Suc x) t') \<longrightarrow> \<not> TypedStoSubpref subL destl (STArray (Suc x) t'))"
  shows "(\<forall>subL. TypedStoSubpref subL srcl (STArray x t') \<longrightarrow> \<not> TypedStoSubpref subL destl (STArray x t'))" 
proof intros
  fix subL
  assume "TypedStoSubpref subL srcl (STArray x t')"
  then have "TypedStoSubpref subL srcl (STArray (Suc x) t')" by auto
  then have "\<not> TypedStoSubpref subL destl (STArray (Suc x) t')" using assms by blast
  then show " \<not> TypedStoSubpref subL destl (STArray x t')" by simp
qed

lemma dhsuhdua:
  assumes "\<forall>destl'. \<not> TypedStoSubpref destl' destl t' \<longrightarrow> (\<forall>t. accessStorage t destl' srcMem = accessStorage t destl' v')"
    and "    \<forall>subL. TypedStoSubpref subL srcl t' \<longrightarrow> \<not> TypedStoSubpref subL destl t'"
    and "    SCon t' srcl srcMem" 
  shows "SCon t' srcl v'" using assms
proof(induction t' arbitrary:srcl)
  case (STArray x1 t')
  then show ?case 
    by (meson Scon_NoChange)
next
  case (STMap x1 t')
  then show ?case 
    by (meson Scon_NoChange)
next
  case (STValue x)
  then show ?case by simp
qed










lemma CompStoType_sharedSub:
  assumes "CompStoType pParentT tp1 pParentPtr p"
    and "TypedStoSubpref p stl2 tp2"
    and "CompStoType pParentT tp2 pParentPtr stl2"
  shows "CompStoType tp2 tp1 stl2 p " using assms
proof(induction tp2 arbitrary: stl2)
  case (STArray x1 tp2)
  then have cc:"p = stl2 \<or> (\<exists>i<x1. TypedStoSubpref p (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) tp2)" unfolding TypedStoSubpref.simps by simp
  then show ?case 
  proof(cases "p = stl2")
    case True
    then show ?thesis 
      using CompStoType_sameLocNdTyp CompStoType_sameLocs_sameType STArray.prems(2) STArray by blast
  next
    case False
    then show ?thesis 
      by (meson CompStoType_sameLocNdTyp CompStoType_trns STArray.IH STArray.prems cc CompStoType.simps(2))
  qed
next
  case (STMap x1 tp2)
  then have cc:"p = stl2 \<or> (\<exists>i. typeCon x1 i \<and> TypedStoSubpref p (hash stl2 i) tp2)" 
    unfolding TypedStoSubpref.simps by simp
  then show ?case 
  proof(cases "p = stl2")
    case True
    then show ?thesis 
      using CompStoType_sameLocs_sameType STMap.prems by simp
  next
    case False
    then obtain i where idef:"(typeCon x1 i \<and> TypedStoSubpref p (hash stl2 i) tp2)" using cc by blast
    then show ?thesis using STMap.IH[of "(hash stl2 i)"] 
      by (meson CompStoType_sameLocNdTyp CompStoType_trns STMap.prems  CompStoType.simps(3))
  qed
next
  case (STValue x)
  then show ?case  
    by (simp add: CompStoType_sameLocs_sameType)
qed

lemma dasdas:
  assumes "TypedStoSubpref destl prnt tp"
  shows "location_depth destl \<ge> location_depth prnt \<and> location_depth destl \<le>  location_depth prnt + stype_size tp"
  using assms
proof(induction tp arbitrary:prnt)
  case (STArray x1 tp)
  then show ?case 
    by (metis (no_types, lifting) ShowLNatDot TypedStoSubpref.simps(2) ab_semigroup_add_class.add_ac(1) hash_adds_depth linorder_not_le
        not_add_less1 order_le_less stype_size.simps(2) subloc_deeper)
next
  case (STMap x1 tp)
  then show ?case 
    by (metis (no_types, lifting) TypedStoSubpref.simps(3) ab_semigroup_add_class.add_ac(1) hash_adds_depth le_add1 order_le_less
        stype_size.simps(3) subloc_deeper typeConNoDots)
next
  case (STValue x)
  then show ?case 
    by auto
qed

lemma Sto_divergence_imps_notsubloc_allsubloc:
  assumes "\<not>TypedStoSubpref (hash destl x) destl tp"
    and "CHR ''.'' \<notin> set(String.explode x)"
  shows "\<not>TypedStoSubpref (hash (hash destl x) y) destl tp"
proof
  assume asm4:"TypedStoSubpref (hash (hash destl x) y) destl tp"
  then have "hash destl x \<noteq> destl" using ShowLNatDot 
    using hash_inequality by auto
  show False using asm4 assms(1,2)
  proof (cases tp)
    case (STArray x1 tp)
    have *:"hash (hash destl x) y = destl \<or> (\<exists>i<x1. TypedStoSubpref (hash (hash destl x) y) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) tp)" 
      using asm4 STArray unfolding TypedStoSubpref.simps by simp
    then have "hash (hash destl x) y \<noteq> destl" using hash_injective ShowLNatDot  Read_Show_nat'_id readLintNotEqual * 
        TypedStoSubpref_hashes TypedStoSubpref_sameLoc assms(2) 
      by (metis hash_suffixes_associative)
    then obtain ia where " ia <x1 \<and> TypedStoSubpref (hash (hash destl x) y) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t ia)) tp" using * by auto
    then have a3:"TypedStoSubpref (hash destl (hash x y)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t ia)) tp" 
      by (simp add: hash_suffixes_associative)
    then have " (hash x y) \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t ia)" using hash_def ShowLNatDot 
      by (metis subPrefCannotBeInt)
    then show ?thesis
      using a3 hash_injective ShowLNatDot TypedStoSubpref_child_imps_prnt TypedStoSubpref_hashes hash_never_equal_sufix
      by (smt (verit) NotRelatedPrnt_imps_notRelatedChild TypedStoSubpref_b asm4 assms(1,2) hash_suffixes_associative hashesAssociative)
  next
    case (STMap x1 tp)
    have *:"hash (hash destl x) y = destl \<or> (\<exists>ia. typeCon x1 ia \<and> TypedStoSubpref (hash (hash destl x) y) (hash destl ia) tp)" 
      using asm4 STMap unfolding TypedStoSubpref.simps by simp
    then have "hash (hash destl x) y \<noteq> destl" using hash_injective ShowLNatDot  Read_Show_nat'_id readLintNotEqual * 
        TypedStoSubpref_hashes TypedStoSubpref_sameLoc assms(2) 
      by (metis hash_suffixes_associative)
    then obtain ia where ag:"typeCon x1 ia \<and> TypedStoSubpref (hash (hash destl x) y) (hash destl ia) tp" using * by auto
    then have a3:"TypedStoSubpref (hash destl (hash x y)) (hash destl ia) tp" 
      by (simp add: hash_suffixes_associative)
    then have " (hash x y) \<noteq> ia" using hash_def ShowLNatDot typeConNoDots ag 
      using subPrefCannotBeInt by blast
    then show ?thesis using a3 hash_injective ShowLNatDot TypedStoSubpref_child_imps_prnt TypedStoSubpref_hashes hash_never_equal_sufix NotRelatedPrnt_imps_notRelatedChild TypedStoSubpref_b asm4 assms(1,2) hash_suffixes_associative hashesAssociative       
      by (smt (verit) STMap TypedStoSubpref.simps(3) typeConNoDots)
  next
    case (STValue x')
    then show ?thesis 
      using asm4 hash_inequality hash_suffixes_associative by auto 
  qed
qed


lemma SCon_sub_imps_Parent:
  assumes "    CompStoType struct (STArray x t''') x4 p'"
    and "SCon (STArray x t''') p' (storage st' (address env))"
    and "SCon struct x4 (storage st (address env))"
    and "t' = STArray x t''' "
    and "\<forall>locs t''. locs \<noteq> p' \<and> \<not> TypedStoSubpref locs p' (STArray x t''') \<longrightarrow>
       accessStorage t'' locs (storage st (address env)) = accessStorage t'' locs (storage st' (address env))" 
  shows "SCon struct x4 (storage st' (address env))" using assms(1,2,3)
proof(induction struct arbitrary: x4)
  case (STArray x1 struct)
  have c:"STArray x t''' = STArray x1 struct \<and> x4 = p' \<or> (\<exists>i<x1. CompStoType struct (STArray x t''') (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) p')" 
    using STArray(2) unfolding CompStoType.simps by blast

  then show ?case 
  proof(cases "x4 = p'")
    case True
    then have "STArray x t''' = STArray x1 struct" using c 
      using CompStoType_sameLoc_sameType STArray.prems(1) by blast
    then show ?thesis using assms True by auto
  next
    case False
    then obtain i where idef:"(i<x1 \<and> CompStoType struct (STArray x t''') (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) p')" using c by auto
    then have sc:"SCon struct (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (storage st' (address env))"
      using STArray.IH[of "(hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i))"] STArray(3) 
      using STArray.prems(3) by auto
    have " \<forall>i<x1. SCon struct (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (storage st' (address env))"
    proof intros
      fix i'' assume *:"i''<x1" 
      then show "SCon struct (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (storage st' (address env))"
      proof(cases "i'' = i")
        case True
        then show ?thesis using idef sc by simp
      next
        case False
        then have "\<not>CompStoType struct (STArray x t''') (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) p'" 
          using idef 
          by (metis CompStoType_unique_location ShowLNatDot hashesIntSame)
        then have g:"\<not>TypedStoSubpref p' (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) struct" 
          by (metis CompStoType_imps_TypedStoSubpref NotRelatedPrnt_imps_notRelatedChild ShowLNatDot
              hash_adds_depth idef same_depth_imp_neg_TypedStoSubpref)
        have g5:"\<not> TypedStoSubpref (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) p' (STArray x t''')" 
          by (metis CompStoType_imps_TypedStoSubpref STArray.prems(1) ShowLNatDot
              TypedStoSubpref_child_imps_prnt TypedStoSubpref_hashes g idef
              typedStoSub_imps_negInv)
        have g6:"\<forall>l. \<not> TypedStoSubpref (hash (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) l) p' (STArray x t''')" 
          using CompStoType_imps_subloc False TypedStoSubpref_b hash_flatten_right hashesInts
              idef
          by (smt (verit, best) )
        have g2:"SCon struct (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (storage st (address env))" using STArray(4) 
          by (simp add: "*")
        then show ?thesis using assms CompStoType_imp_subType sublocs_nonchanged_SCon[OF g  ] g5 g6 by blast 
      qed
    qed
    then show ?thesis unfolding SCon.simps by simp
  qed

next
  case (STMap x1 struct)
  obtain i where idef:"(typeCon x1 i \<and> CompStoType struct (STArray x t''') (hash x4 i) p')" 
    using STMap(2) unfolding CompStoType.simps by blast
  then have sc:"SCon struct (hash x4 i) (storage st' (address env))"
    using STMap.IH[of "(hash x4 i)"] STMap(3) 
    using STMap.prems(3) by auto
  have "\<forall>i. typeCon x1 i \<longrightarrow> SCon struct (hash x4 i) (storage st' (address env))"
  proof intros
    fix i'' assume *:"typeCon x1 i''"
    then show "SCon struct (hash x4 i'') (storage st' (address env))"
    proof(cases "i'' = i")
      case True
      then show ?thesis using idef sc by simp
    next
      case False
      then have "\<not>CompStoType struct (STArray x t''') (hash x4 i'') p'" using idef 
        using "*" CompStoType_unique_location typeConNoDots by blast
      then have g:"\<not>TypedStoSubpref p' (hash x4 i'') struct"         
        by (smt (verit, ccfv_SIG) "*" CompStoType_imps_subloc CompStoType_sameLoc_sameType False LSubPrefL2_def STMap.prems(1) typeCon_no_sublocation_prefix TypedStoSubpref_b
            TypedStoSubpref_hashes Mutual_NonSub_SpecificNonSub Not_Sub_More_Specific hash_inequality hash_never_equal_sufix hash_suffixes_associative idef php1 TypedStoSubpref.simps(3)
            assms)
      have g5:"\<not> TypedStoSubpref (hash x4 i'') p' (STArray x t''')" 
        by (smt (verit, ccfv_SIG) "*" CompStoType_imps_subloc LSubPrefL2_def typeCon_no_sublocation_prefix TypedStoSubpref_b TypedStoSubpref_sameLoc
            \<open>\<And>thesis. (\<And>i. typeCon x1 i \<and> CompStoType struct (STArray x t''') (hash x4 i) p' \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> g hash_suffixes_associative)
      then have g6:"\<forall>l. \<not> TypedStoSubpref (hash (hash x4 i'') l) p' (STArray x t''')" 
        by (smt (verit, best) "*" CompStoType_imps_subloc CompStoType_sameLoc_sameType False LSubPrefL2_def STMap.prems(1) STypes.distinct(1) typeCon_no_sublocation_prefix
            TypedStoSubpref_b Mutual_NonSub_SpecificNonSub hash_never_equal_sufix idef)
      have g2:"SCon struct (hash x4 i'') (storage st (address env))" using STMap(4) 
        by (simp add: "*")
      then show ?thesis using assms CompStoType_imp_subType sublocs_nonchanged_SCon[OF g assms(5) g2] g5 g6 by blast 
    qed
  qed
  then show ?case unfolding SCon.simps 
    by simp
next
  case (STValue x)
  then show ?case by simp
qed



end