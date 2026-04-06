# NotebookLM Oracle — Slide Deck & Audio Podcast Generator

Generate beautiful slide decks and audio podcasts from paper PDFs via Google NotebookLM,
then push them to standalone GitHub repos for promotion.

```
notebooklm_dispatch.py  -->  notebooklm-py RPC  -->  NotebookLM API
        |                                                    |
        v                                                    v
  artifacts/slug/                              slide_deck.pdf + podcast.wav
        |
        v
  create_paper_repos.py  -->  GitHub repos with media/
```

## Setup

```bash
pip install notebooklm-py
notebooklm login          # Opens browser for Google auth
```

## Usage

```bash
# Generate slides + audio for one paper
python notebooklm_dispatch.py --paper /path/to/paper_dir

# Audio only
python notebooklm_dispatch.py --paper /path/to/paper_dir --type audio

# Slides only
python notebooklm_dispatch.py --paper /path/to/paper_dir --type slides

# All submitted papers
python notebooklm_dispatch.py --all

# Queue without waiting (check later)
python notebooklm_dispatch.py --paper /path/to/paper_dir --no-wait

# Check artifact status
python notebooklm_dispatch.py --notebook <id> --status

# Download completed artifacts
python notebooklm_dispatch.py --notebook <id> --download

# List all notebooks
python notebooklm_dispatch.py --list
```

Artifacts save to `papers/publication/notebooklm/artifacts/<slug>/`.

## Integration with Paper Repos

`create_paper_repos.py` automatically detects artifacts in `notebooklm/artifacts/`
and includes them in the `media/` directory of each standalone GitHub repo.

## Files

| File | What |
|------|------|
| `notebooklm_dispatch.py` | CLI — upload PDF, generate slides/audio, download |
| `notebooklm_oracle.user.js` | Tampermonkey userscript (legacy, for reference) |
| `notebooklm_server.py` | HTTP bridge server (legacy) |
| `notebooklm_pipeline.py` | Template-based content pipeline |

## Requirements

- Python 3.10+ (stdlib only)
- `notebooklm-py` (`pip install notebooklm-py`)
- Google account with NotebookLM access

## License

MIT
