from flask import render_template, request, session, redirect, url_for

class UserManager:
    def __init__(self, db_manager, session):
        self.db_manager = db_manager
        self.session = session

    def is_signed_in(self):
        return 'email' in session

    def user_exists(self, email):
        existing_user = self.db_manager.execute_query("SELECT * FROM users WHERE email = %s", (email,))
        return existing_user

    def add_user(self):
        email = request.form['email']
        password = request.form['password']

        if self.user_exists(email):
            return render_template('index.html', error2="Email already exists.")
        
        insert_query = "INSERT INTO users (email, password) VALUES (%s, %s)"
        self.db_manager.execute_commit(insert_query, (email, password))

        return render_template('index.html', success2="Registration successful! You may now log in.")

    def login(self):
        if request.method == 'POST':
            email = request.form['email']
            password = request.form['password']

            query = "SELECT * FROM users WHERE email = %s AND password = %s"
            user = self.db_manager.execute_query(query, (email, password))

            if user:
                session['email'] = email
                return redirect(url_for('home'))
            else:
                return render_template('login.html', error='Invalid email or password')

        return render_template('login.html', error=None)

    def logout(self):
        session.pop('email', None)
        return redirect(url_for('index'))
