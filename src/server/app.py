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
        

        user_email = session['email']  # Get the logged-in user's email
        quizzes = quiz_manager.get_user_quizzes(user_email)  # Fetch quizzes

        return render_template('home.html', quizzes=quizzes)  # Pass quizzes to the template

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


    @app.route('/quiz/<int:quiz_id>')
    def quiz_detail_route(quiz_id):
        # Call the QuizManager to get the quiz details
        quiz = quiz_manager.get_quiz_by_id(quiz_id)

        # If the quiz is not found, return an error or flash a message
        if not quiz:
            return "Quiz not found", 404

        # Render the quiz detail page with the quiz data
        return render_template('quiz-detail.html', quiz=quiz)

    @app.route('/take-quiz/<int:quiz_id>', methods=['GET'])
    def take_quiz_route(quiz_id):
        # Fetch the quiz details including the questions
        quiz = quiz_manager.get_quiz_by_id(quiz_id)
        
        if not quiz:
            return "Quiz not found", 404

        # Render the quiz taking form
        return render_template('take-quiz.html', quiz=quiz, quiz_id=quiz_id)
    
    @app.route('/submit-quiz-answers/<int:quiz_id>', methods=['POST'])
    def submit_quiz_answers_route(quiz_id):
        # Fetch the quiz details
        quiz = quiz_manager.get_quiz_by_id(quiz_id)
        
        # Get the user's answers from the form
        user_answers = []
        for i in range(len(quiz['questions'])):
            user_answers.append(request.form.get(f'answer_{i}'))  # This will get 'A', 'B', 'C', or 'D'

        # Compare answers and calculate score
        score = 0
        for i in range(len(quiz['questions'])):
            if user_answers[i] == quiz['questions'][i]['correct_option']:
                score += 1
        
        # Pass the score to the score.html template
        return render_template('score.html', score=score, total=len(quiz['questions']))



    return app

def main():
    app = create_app()  # Call the function to initialize the app
    app.run(debug=True)  # Start the Flask application

if __name__ == '__main__':
    main()
