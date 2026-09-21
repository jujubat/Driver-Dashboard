# Driver Dashboard v46

## Important fixes
- `index.html` is now the v46 dashboard, so Render serves the updated interface instead of the old v43 page.
- Backend is correctly named `server.py` to match the Render start command.
- Removed the broken browser/API-key mismatch that blocked SQL driver login.
- Attendance exception reasons, notes, late proof and manager/admin override proof are persisted in SQL.
- v45 requested roster/mobile/theme/store/biometric/download features are retained once, without a second duplicate dashboard file being served.

## Render
Upload/push this package to GitHub. Render runs:
`uvicorn server:app --host 0.0.0.0 --port $PORT`

Persistent SQLite remains mounted at `/var/data`.
