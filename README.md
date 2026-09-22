# Kotak Market Studio V2
Professional browser/mobile stock + mutual fund research dashboard.

## Render
Upload all files/folders to one GitHub repo. Keep `templates` and `static` folders exactly as-is. Add Render environment variables from `.env.example`; never commit secrets.

## Local test
`pip install -r requirements.txt` then `python app.py`, open http://127.0.0.1:5000

Excel export is formatted with freeze header, filters and auto column widths. Blank Top Results safely defaults to 20.
