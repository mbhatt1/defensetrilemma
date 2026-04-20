from trilemma_validator.cli import build_parser
p = build_parser()
for action in p._actions:
    if hasattr(action, 'choices') and action.choices is not None:
        cmds = sorted(action.choices.keys())
        print('subcommands:', cmds)
        expected = {'pipeline','validate','sweep','experiment','synth','sensitivity','csweep','resolution'}
        missing = expected - set(cmds)
        extra = set(cmds) - expected
        if missing:
            print('MISSING:', missing)
        if extra:
            print('EXTRA:', extra)
        print('count:', len(cmds))
        break
