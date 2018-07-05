#!/usr/bin/env bash -x

rm -rf $(isabelle getenv ISABELLE_OUTPUT | cut -d= -f2)
