COQBIN=
-include ../CONFIGURE
unifysl_dir := ..
coq_exe		:= $(COQBIN)coqc
coq_flags	:= -R $(unifysl_dir) Logic
src         := Generate.v
dst         := Generated.v

.PHONY: all clean

all: $(dst)

Config.vo: Config.v
	$(coq_exe) $(coq_flags) Config.v

GeneratedGenerate.v: Config.vo
	$(coq_exe) $(coq_flags) GenerateGenerate.v > GeneratedGenerate.v

GeneratedGenerate.vo: GeneratedGenerate.v
	$(coq_exe) $(coq_flags) GeneratedGenerate.v

$(dst): $(src) Config.vo GeneratedGenerate.vo
	$(coq_exe) $(coq_flags) $(src) > $@

clean:
	@rm -rf *.vo *.glob .*.aux $(dst) 2>/dev/null
