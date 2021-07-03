GEN_LEMMAS = ../t-cheri/tools/gen_lemmas
MORELLO_DIR = ../arm-morello-dropzone

EXTRA_FLAGS = -splice ${MORELLO_DIR}/patches/translation_stubs.sail -splice ${MORELLO_DIR}/patches/archex_stubs.sail -splice ${MORELLO_DIR}/patches/unknown_capability.sail -splice ${MORELLO_DIR}/patches/write_tag.sail

gen_lemmas: morello.json
	${GEN_LEMMAS} -src_dir ${MORELLO_DIR}/sail ${EXTRA_FLAGS} morello.json
