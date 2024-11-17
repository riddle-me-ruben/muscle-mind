from flask import render_template, request, session, redirect, url_for

"""
Description:
The UserManager class handles user-related actions, including registration, login, logout, and session tracking. 
It interacts with the database to validate user credentials and manage user data, ensuring secure and efficient 
user management.

Semi-formal Notation:
/*@ requires db_manager != null (valid DatabaseManager instance) &&
  @ session is a valid session object;
  @ ensures UserManager facilitates:
  @   - User registration through add_user;
  @   - User authentication and login via login;
  @   - User logout and session clearing via logout;
  @   - Session-based tracking of login status through is_signed_in;
@*/
"""
class UserManager:
    """
    Description:
    Initializes the UserManager with a DatabaseManager for database operations and a session object for tracking 
    user information.

    Semi-formal Notation:
    /*@ requires db_manager != null (valid DatabaseManager instance) &&
    @ session is a valid session object;
    @ ensures self.db_manager == db_manager &&
    @ ensures self.session == session;
    @*/
    """
    def __init__(self, db_manager, session):
        self.db_manager = db_manager
        self.session = session

    """
    Description:
    Checks whether the current user is signed in by verifying the presence of the 'email' key in the session object.

    Semi-formal Notation:
    /*@ requires session is a valid session object;
    @ ensures \result == ('email' in session);
    @*/
    """
    def is_signed_in(self):
        return 'email' in session

    """
    Description:
    Checks if a user exists in the database using the provided email address. Queries the `users` table to find a 
    matching email.

    Semi-formal Notation:
    /*@ requires email is a valid non-empty string &&
    @ db_manager.execute_query(query, params) functions correctly;
    @ ensures If email exists in the `users` table:
    @   \result == Row of user data matching the email;
    @ ensures If email does not exist in the `users` table:
    @   \result == None;
    @*/
    """
    def user_exists(self, email):
        existing_user = self.db_manager.execute_query("SELECT * FROM users WHERE email = %s", (email,))
        return existing_user

    """
    Description:
    Registers a new user in the database using the provided email and password. Validates that the email is unique 
    before insertion.

    Semi-formal Notation:
    /*@ requires request.form contains 'email' and 'password' fields &&
    @ email is unique in the `users` table;
    @ ensures If email is unique:
    @   Inserts a new row into `users` table with email and password &&
    @   Renders 'index.html' with success message;
    @ ensures If email is not unique:
    @   Renders 'index.html' with error message;
    @*/
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
    Description:
    Authenticates a user by checking their email and password against the database. If valid, logs the user in by 
    storing their email in the session and redirects them to the home page.

    Semi-formal Notation:
    /*@ requires request.method == 'POST' &&
    @ request.form contains 'email' and 'password' fields &&
    @ db_manager.execute_query(query, params) functions correctly;
    @ ensures If email and password match a row in the `users` table:
    @   session['email'] == email &&
    @   Redirects to 'home';
    @ ensures If email or password are invalid:
    @   Renders 'login.html' with error message;
    @*/
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
    Description:
    Logs out the current user by clearing their session data and redirecting them to the index page.

    Semi-formal Notation:
    /*@ requires 'email' in session (user is logged in);
    @ ensures session['email'] == None &&
    @ ensures session['other_user_email'] == None &&
    @ ensures Redirects to 'index';
    @*/
    """
    def logout(self):
        session.pop('email', None)
        session.pop('other_user_email', None)
        return redirect(url_for('index'))