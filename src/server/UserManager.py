from flask import render_template, request, session, redirect, url_for

class UserManager:
    """
    Initialize the UserManager with a database manager and session object
    db_manager: DatabaseManager - The manager responsible for database operations
    session: dict - The session object for tracking user information
    @requires A valid DatabaseManager and session object
    @ensures UserManager is ready to handle user-related tasks such as login, logout, and registration
    """
    def __init__(self, db_manager, session):
        self.db_manager = db_manager
        self.session = session

    """
    Check if the user is currently signed in
    @requires A session object that tracks user login status
    @ensures Returns True if the user is signed in, False otherwise
    """
    def is_signed_in(self):
        return 'email' in session

    """
    Check if a user exists in the database with the provided email
    email: str - The email address to check for existence
    @requires A valid email string
    @ensures Returns the existing user data if the user exists, None otherwise
    """
    def user_exists(self, email):
        existing_user = self.db_manager.execute_query("SELECT * FROM users WHERE email = %s", (email,))
        return existing_user

    """
    Add a new user to the database
    @requires The email and password fields to be provided in the request form
    @ensures Adds the user to the database if the email is not already taken, or displays an error message
    """
    def add_user(self):
        email = request.form['email']
        password = request.form['password']

        if self.user_exists(email):
            return render_template('index.html', error2="Email already exists.")
        
        insert_query = "INSERT INTO users (email, password) VALUES (%s, %s)"
        self.db_manager.execute_commit(insert_query, (email, password))

        return render_template('index.html', success2="Registration successful! You may now log in.")

    """
    Log in the user by checking their credentials
    @requires The email and password fields to be provided in the request form
    @ensures If credentials are valid, the user is logged in and redirected to the home page, otherwise an error is displayed
    """
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

    """
    Log out the user by clearing the session
    @requires The user to be logged in (i.e., 'email' key exists in session)
    @ensures The session is cleared and the user is redirected to the index page
    """
    def logout(self):
        session.pop('email', None)
        return redirect(url_for('index'))
