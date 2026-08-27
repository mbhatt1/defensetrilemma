# Defense Trilemma reproduction Makefile.
#
# Targets:
#   make validate      — rerun the saturated-archive validator runs
#   make tables        — regenerate all auto-generated tables from JSON
#   make figures       — regenerate all figures
#   make paper         — compile paper2_v3.pdf and paper2_v3_submission.pdf
#   make zip           — rebuild defense_trilemma_overleaf.zip
#   make clean         — remove LaTeX aux/log files (keeps PDFs)
#   make clean-all     — also remove generated PDFs
#   make all           — tables + figures + paper + zip
#
# Environment:
#   OPENAI_API_KEY must be set for validator targets that touch the
#   OpenAI API (retarget, rescore, PAIR, paraphrase).

PY          ?= python3
TRILEMMA    ?= $(HOME)/Library/Python/3.9/bin/trilemma
REPO        := $(CURDIR)
VAL_ROOT    := $(REPO)/trilemma_validator
SCRIPTS     := $(VAL_ROOT)/scripts
LIVE_RUNS   := $(VAL_ROOT)/live_runs
OVERLEAF    := $(REPO)/overleaf_package

SATURATED_ARCHIVE := $(LIVE_RUNS)/gpt35_turbo_t05_saturated/source_archive.json
HARM_YAML         := $(HOME)/rethinking-evals/config/harm_categories.yaml

.PHONY: all validate tables figures paper zip clean clean-all help check-api

help:
	@grep -E '^# ' $(firstword $(MAKEFILE_LIST)) | sed 's/^# //'

# ----- sanity checks -----

check-api:
	@if [ -z "$$OPENAI_API_KEY" ]; then \
	  echo "ERROR: OPENAI_API_KEY is not set"; exit 1; \
	fi

# ----- defaults -----

all: tables figures paper zip

# ----- validator re-runs on existing archives -----

validate:
	@echo "[$$(date +%H:%M:%S)] validator: saturated archive"
	$(TRILEMMA) validate --archive $(SATURATED_ARCHIVE) --tau 0.5 \
	  --defense smooth_nearest_safe --bootstrap 1000 \
	  --output $(LIVE_RUNS)/gpt35_turbo_t05_saturated/validate_smooth.json
	$(TRILEMMA) csweep --archive $(SATURATED_ARCHIVE) --tau 0.5 \
	  --out $(LIVE_RUNS)/gpt35_turbo_t05_saturated/continuous_sweep
	$(TRILEMMA) sensitivity --archive $(SATURATED_ARCHIVE) --tau 0.5 \
	  --out $(LIVE_RUNS)/gpt35_turbo_t05_saturated/sensitivity
	$(TRILEMMA) resolution --archive $(SATURATED_ARCHIVE) --tau 0.5 \
	  --out $(LIVE_RUNS)/gpt35_turbo_t05_saturated/resolution

# ----- tables + figures regen from stored data -----

tables:
	$(PY) $(SCRIPTS)/regen_ci_table_final.py
	$(PY) $(SCRIPTS)/analyze_judges.py \
	  --archives \
	    "gpt-4.1-2025-04-14:$(LIVE_RUNS)/gpt35_turbo_t05_saturated/source_archive.json" \
	    "gpt-4o-2024-08-06:$(LIVE_RUNS)/gpt35_turbo_t05_judge_gpt4o/source_archive.json" \
	    "gpt-4.1-mini-2025-04-14:$(LIVE_RUNS)/gpt35_turbo_t05_judge_gpt41_mini/source_archive.json" \
	    "gpt-4o-mini-2024-07-18:$(LIVE_RUNS)/gpt35_turbo_t05_judge_gpt4o_mini/source_archive.json" \
	  --tau 0.5 \
	  --out-tex $(REPO)/tables/judge_robustness.tex \
	  --out-md  $(LIVE_RUNS)/judge_robustness_report.md \
	  --out-json $(LIVE_RUNS)/judge_robustness_deltas.json
	$(PY) $(SCRIPTS)/judge_committee.py
	$(PY) $(SCRIPTS)/pipeline_demo.py
	$(PY) $(SCRIPTS)/higher_dim_lipschitz.py \
	  --source $(SATURATED_ARCHIVE) \
	  --tex-out $(REPO)/tables/higher_dim_lipschitz.tex \
	  --md-out  $(REPO)/outputs/higher_dim_lipschitz.md \
	  --json-out $(LIVE_RUNS)/higher_dim_lipschitz.json

figures:
	PYTHONPATH=$(VAL_ROOT)/src $(PY) $(SCRIPTS)/make_paper_figure.py \
	  --length-scale 0.20 --alpha-step 0.003 --sigmoid-steepness 2.0 \
	  --noise 0.02 --oblique-angle 89.5
	$(PY) $(SCRIPTS)/make_fig_stochastic_histogram.py
	$(PY) $(SCRIPTS)/make_fig_judge_scatter_real.py

# ----- paper -----

paper:
	pdflatex -interaction=nonstopmode paper2_v3.tex
	pdflatex -interaction=nonstopmode paper2_v3.tex
	-[ -f paper2_v3_submission.tex ] && pdflatex -interaction=nonstopmode paper2_v3_submission.tex
	-[ -f paper2_v3_submission.tex ] && pdflatex -interaction=nonstopmode paper2_v3_submission.tex

zip: paper
	cp paper2_v3.tex $(OVERLEAF)/
	-[ -f paper2_v3_submission.tex ] && cp paper2_v3_submission.tex $(OVERLEAF)/
	cp tables/*.tex $(OVERLEAF)/tables/
	cp figures/*.pdf $(OVERLEAF)/figures/
	rm -f defense_trilemma_overleaf.zip
	(cd $(OVERLEAF) && zip -rq ../defense_trilemma_overleaf.zip . \
	  -x "*.DS_Store" "*.aux" "*.log" "*.out" "*.pdf")

clean:
	rm -f *.aux *.log *.out *.toc *.fls *.fdb_latexmk

clean-all: clean
	rm -f *.pdf defense_trilemma_overleaf.zip
