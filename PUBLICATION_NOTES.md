# Public edition

This repository assembles the 2026-10-16 transfer-bound research record. Human review is incomplete.

- Current technical documents keep their original filenames so cross-references remain usable.
- Review banners were added; historical snapshots are labelled as historical.
- Literal bars inside table code spans were escaped for Markdown rendering.
- Machine-specific paths were replaced by placeholders or portable executable names. Logs retain numerical outputs, errors, and test results, but are therefore not byte-identical raw machine logs.
- Julia research scripts, including failed versions, are byte-identical copies. PUBLICATION_PROVENANCE.json records both source and public SHA-256 values.
- The original integrity and deliverable manifests describe the **local research snapshot**. Their old hashes do not authenticate edited public Markdown. Use PUBLICATION_PROVENANCE.json for the public copies.
- Original PowerShell runners were replaced by portable entry points. Historical environment logs may still record the hashes of those original runners.
- The literature audit describes downloads and rendered pages used locally. PDF/HTML caches, source archives and rendered paper images are not bundled. External URLs remain in the literature audit.
- The upstream certificate/verifier can be fetched with the pinned hashes in scripts/fetch_reference.py. The retained verification log is a rerun of the author's verifier.

The MIT license applies to original project material. It does not relicense referenced third-party work.
