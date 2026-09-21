# Driver Dashboard v47

Driver roster changes in v47:
- Drivers are added to the roster automatically after successful first registration/login; manual Add Driver/Add Me to Roster controls were removed.
- First registration requires full names, email, password (6+ characters), and phone number. Returning drivers use email + password; biometrics/passkeys can be enabled after registration.
- Driver greeting shows Good morning/afternoon/evening + driver name.
- No-photo reasons include Personal reason and save as Pending Approval for Admin/Manager review.
- Store picker keeps custom Add Store as the final option.
- Theme choices are Device, Black, White.
- Logout is a dedicated visible button.
- Responsive layout remains device-agnostic for Android/Huawei/iPhone/iPad/tablet/laptop/desktop.

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
