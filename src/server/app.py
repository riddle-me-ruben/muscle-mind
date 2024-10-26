from flask import Flask, render_template, request, redirect, url_for, session
from DatabaseManager import DatabaseManager
from QuizManager import QuizManager
from dotenv import load_dotenv
import os

# Load environment variables
load_dotenv()

def create_app():
    # Initialize Flask app
    app = Flask(__name__, static_folder=os.path.join(os.path.dirname(__file__), '../../static'), template_folder='../client')
    app.config['SECRET_KEY'] = os.getenv('SECRET_KEY')

    # Initialize the DatabaseManager instance and configure the database
    db_manager = DatabaseManager(app)

    # Create an instance of the QuizManager class
    quiz_manager = QuizManager(db_manager, session)

    # Helper function to check if the user is signed in
    def is_signed_in():
        return 'email' in session

    # Helper function to check if a user exists in the database
    def user_exists(email):
        existing_user = db_manager.execute_query("SELECT * FROM users WHERE email = %s", (email,))
        return existing_user

    # Define routes within the create_app function to keep state within app context
    @app.route('/')
    def index():
        if is_signed_in():
            return redirect(url_for('home'))  # Redirect if already logged in
        
        return render_template('index.html')  # Show login/signup options

    @app.route('/add_user', methods=['POST'])
    def add_user():
        email = request.form['email']
        password = request.form['password']

        # Check if the email already exists
        if user_exists(email):
            return render_template('index.html', error2="Email already exists.")

        # Insert the new user if the email does not exist
        insert_query = "INSERT INTO users (email, password) VALUES (%s, %s)"
        db_manager.execute_commit(insert_query, (email, password))

        return render_template('index.html', success2="Registration successful! You may now log in.")

    @app.route('/login', methods=['GET', 'POST'])
    def login():
        if request.method == 'POST':
            email = request.form['email']
            password = request.form['password']

            # Verify user credentials
            query = "SELECT * FROM users WHERE email = %s AND password = %s"
            user = db_manager.execute_query(query, (email, password))

            if user:
                session['email'] = email  # Store the user's email in the session
                return redirect(url_for('home'))
            else:
                return render_template('login.html', error='Invalid email or password')

        return render_template('login.html', error=None)

    @app.route('/home')
    def home():
        if not is_signed_in():
            return redirect(url_for('login'))  # Redirect if not logged in
        return render_template('home.html')  # Render home page if logged in

    @app.route('/logout')
    def logout():
        session.pop('email', None)  # Remove user from session
        return redirect(url_for('index'))

    # Route to render the quiz creation form
    @app.route('/create-quiz', methods=['GET', 'POST'])
    def create_quiz_route():
        if request.method == 'POST':
            return quiz_manager.create_quiz()
        return render_template('create-quiz.html')  # Renders the form for number of questions


    # Route to handle the quiz submission
    @app.route('/submit-quiz', methods=['POST'])
    def submit_quiz_route():
        return quiz_manager.submit_quiz()

    return app

def main():
    app = create_app()  # Call the function to initialize the app
    app.run(debug=True)  # Start the Flask application

if __name__ == '__main__':
    main()
