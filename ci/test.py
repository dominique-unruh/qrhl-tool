import os
import sys
from pathlib import Path
import dataclasses

from scala_isabelle_ci.test import TestConfig, do_tests, Settings

def main():
    import argparse, argcomplete
    parser = argparse.ArgumentParser()
    parser.add_argument("--java", type=int)
    parser.add_argument("--num-tests", type=int, default=1)
    parser.add_argument("--show-results", action="store_true")
    parser.add_argument("--no-show-results", action="store_false", dest="show_results")
    argcomplete.autocomplete(parser)
    args = parser.parse_args()

    ci_dir = Path(__file__).absolute().parent
    qrhl_dir = ci_dir.parent
    show_results = args.show_results or (args.num_tests <= 1)
    isabelle_version=qrhl_dir.joinpath("src/main/resources/qrhl/isabellex/isabelleVersion").read_text()
    settings = Settings(ci_dir=ci_dir, main_dir=qrhl_dir, show_results=show_results, isabelle_versions=(isabelle_version,),
                        container_repo_dir="qrhl-tool")
    dataclasses.replace(settings, exclude = settings.exclude + tuple(f"/scala-isabelle{word}" for word in settings.exclude))

    config = TestConfig(isabelle=isabelle_version, java=args.java)
    success = do_tests(settings, config, args.num_tests)
    if not success:
        sys.exit(1)

if __name__ == '__main__':
    main()
