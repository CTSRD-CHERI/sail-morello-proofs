theory CHERI_Fetch_Properties
  imports CHERI_Mem_Properties
begin

context Morello_Fetch_Automaton
begin

lemmas non_cap_exp_traces_enabled[traces_enabledI] = non_cap_expI[THEN non_cap_exp_traces_enabledI]

lemmas non_mem_exp_traces_enabled[traces_enabledI] = non_mem_expI[THEN non_mem_exp_traces_enabledI]

lemma traces_enabled_Mem_read_Fetch[traces_enabledI]:
  assumes "\<And>v. paccess_enabled s Fetch (unat (FullAddress_address (AddressDescriptor_paddress desc))) (nat sz) v B0"
  shows "traces_enabled (Mem_read desc sz accdesc) s"
  unfolding Mem_read_def bind_assoc
  by (traces_enabledI intro: traces_enabled_read_mem assms: assms)

lemma load_enabled_access_enabled_Fetch[intro]:
  assumes "load_enabled s acctype vaddr sz tagged"
    and "sz' = nat sz"
    and "translate_address vaddr = Some paddr"
    and "tagged \<or> tag = B0"
  shows "\<exists>vaddr. access_enabled s Fetch vaddr paddr sz' data tag"
  using assms
  unfolding load_enabled_def
  by (cases tagged) auto

lemma traces_enabled_AArch64_MemSingle_read[traces_enabledI]:
  assumes "translate_address (unat address) \<noteq> None \<longrightarrow> load_enabled s acctype (unat address) size__arg False"
  shows "traces_enabled (AArch64_MemSingle_read address size__arg acctype wasaligned :: 'size_times_p8::len word M) s"
  unfolding AArch64_MemSingle_read_def bind_assoc
  by (traces_enabledI assms: assms intro: traces_enabled_Mem_read_Fetch simp: exp_fails_if_then_else)

lemma traces_enabled_FetchInstr[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (FetchInstr pc) s"
  unfolding FetchInstr_def CheckPCCCapability_def bind_assoc
  by (traces_enabledI assms: assms elim: CheckCapability_load_enabled intro: derivable_or_invokedI1)

end

end