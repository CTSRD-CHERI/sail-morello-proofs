GEN_LEMMAS = ../t-cheri/tools/gen_lemmas
MORELLO_DIR = ../arm-morello-dropzone
PROOF_DIR = $(realpath .)
SAIL = sail

MORELLO_SAIL_DIR = ${MORELLO_DIR}/sail

SMT_SAIL_BASE = prelude.sail builtins.sail v8_base.sail
SMT_SAIL_BASE_PATHS = $(addprefix $(MORELLO_SAIL_DIR)/,$(SMT_SAIL_BASE))

SAIL_FLAGS = -verbose 1 -memo_z3 -no_effects -non_lexical_flow -no_warn
SMT_FLAGS = # -mono_rewrites

EXTRA_GEN_FLAGS = -splice ${MORELLO_DIR}/patches/translation_stubs.sail -splice ${MORELLO_DIR}/patches/archex_stubs.sail

isail: $(SMT_SAIL_BASE_PATHS) properties.sail
	$(SAIL) -i $(SAIL_FLAGS) $^

smt: $(SMT_SAIL_BASE_PATHS) properties.sail
	$(SAIL) -smt $(SAIL_FLAGS) $(SMT_FLAGS) $^

gen_lemmas: morello.json
	${GEN_LEMMAS} -src_dir ${MORELLO_DIR}/sail ${EXTRA_GEN_FLAGS} morello.json
